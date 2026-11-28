import V8CapacityUnifiedScalarIndex
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset

/-! In S5 the quotient digits use one weak composition with slack.
The stars-and-bars count is proved for the actual typed quotient set,
including empty messages. -/
namespace V8CapacityUnified.Scalar
open scoped Classical BigOperators

noncomputable section
set_option linter.unusedSectionVars false

variable {H : Type*} [Fintype H] [DecidableEq H]

abbrev Quotas (H : Type*) [Fintype H] (L : ℕ) :=
  {t : H → Fin (L+1) // (∑ i : H, (t i).val)≤L}

def slackCount {L : ℕ} (t : Quotas H L) : Option H → ℕ
  | none => L-∑ i : H, (t.val i).val
  | some i => (t.val i).val

theorem slack_total {L : ℕ} (t : Quotas H L) :
    (∑ i : Option H, slackCount t i)=L := by
  rw [Fintype.sum_option]
  simp only [slackCount]
  exact Nat.sub_add_cancel t.property

def quotaToSym {L : ℕ} (t : Quotas H L) : Sym (Option H) L := by
  let f : Option H →₀ ℕ := Finsupp.equivFunOnFinite.symm (slackCount t)
  refine ⟨f.toMultiset,?_⟩
  rw [Finsupp.card_toMultiset,Finsupp.sum_fintype]
  · exact slack_total t
  · intro _
    rfl

theorem count_quotaToSym {L : ℕ} (t : Quotas H L) (a : Option H) :
    ((quotaToSym t):Multiset (Option H)).count a=slackCount t a := by
  change (Finsupp.equivFunOnFinite.symm (slackCount t)).toMultiset.count a=_
  rw [Finsupp.count_toMultiset]
  rfl

theorem sym_counts {L : ℕ} (m : Sym (Option H) L) :
    ((m:Multiset (Option H)).count none)+
      (∑ i : H, (m:Multiset (Option H)).count (some i))=L := by
  have hh : (∑ a : Option H, (m:Multiset (Option H)).count a)=L :=
    (Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)).trans m.property
  rwa [Fintype.sum_option] at hh

def symToQuota {L : ℕ} (m : Sym (Option H) L) : Quotas H L := by
  have hb (i : H) : (m:Multiset (Option H)).count (some i)<L+1 := by
    have hc : (m:Multiset (Option H)).count (some i)≤L :=
      (Multiset.count_le_card (some i) (m:Multiset (Option H))).trans_eq m.property
    omega
  refine ⟨fun i => ⟨(m:Multiset (Option H)).count (some i),hb i⟩,?_⟩
  have h := sym_counts m
  change (∑ i : H, (m:Multiset (Option H)).count (some i))≤ L
  omega

def quotaEquiv (L : ℕ) : Quotas H L ≃ Sym (Option H) L where
  toFun := quotaToSym
  invFun := symToQuota
  left_inv t := by
    apply Subtype.ext
    funext a
    apply Fin.ext
    exact count_quotaToSym t (some a)
  right_inv m := by
    apply Subtype.ext
    apply Multiset.ext.mpr
    intro a
    refine (count_quotaToSym (symToQuota m) a).trans ?_
    cases a with
    | none =>
      have h := sym_counts m
      change L-(∑ i : H, (m:Multiset (Option H)).count (some i))=
        (m:Multiset (Option H)).count none
      omega
    | some a => rfl

theorem quota_card (L : ℕ) :
    Fintype.card (Quotas H L)=(Fintype.card H+L).choose (Fintype.card H) := by
  rw [Fintype.card_congr (quotaEquiv L),Sym.card_sym_eq_choose,Fintype.card_option]
  have h : Fintype.card H+1+L-1=Fintype.card H+L := by omega
  rw [h]
  exact (Nat.choose_symm_add (a:=Fintype.card H) (b:=L)).symm

#print axioms slack_total
#print axioms count_quotaToSym
#print axioms quotaEquiv
#print axioms quota_card
end
end V8CapacityUnified.Scalar
