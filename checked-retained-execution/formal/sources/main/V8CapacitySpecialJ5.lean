import V8CapacitySpecialSignatures
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset

/-! The coarse J5 count is derived using an actual finite shell.
Degree d contributes a genuine multiset of size d and a surviving
Taylor-order slot j≥(d+1-P), not independent choices of all k slots. -/
namespace V8CapacitySpecialJ5
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityFeatures V8CapacitySymbolic V8CapacityNativeMatrix
open V8CapacitySpecialSignatures

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {O H : Type*} [CommRing O] [IsDomain O] [Fintype H]

theorem active_degree_cut (π : O) (P k : ℕ) (i : Columns H π P k) :
    (∑ e : H, α P k i.val e)≤DegreeCap P k ∧
      (∑ e : H, α P k i.val e)+1-P≤ i.val.2.val := by
  obtain ⟨m,hm⟩ := i.property
  let d := ∑ e : H, α P k i.val e
  have hD : d≤DegreeCap P k := by
    by_contra hn
    apply hm
    rw [symCol,if_neg hn,MvPolynomial.coeff_zero]
    exact dvd_zero _
  refine ⟨hD,?_⟩
  have hV :=
    feature_dvd (MvPolynomial.C π) k (α P k i.val) i.val.2.val (symInput (R:=O) k)
  change (MvPolynomial.C π)^(d-i.val.2.val)∣feature π k (α P k i.val) i.val.2.val at hV
  obtain ⟨g,hg⟩ := hV
  have hc : (symCol π P k i.val).coeff m=π^(d-i.val.2.val)*g.coeff m := by
    rw [symCol,if_pos hD,hg,← map_pow,MvPolynomial.coeff_C_mul]
  by_contra! h
  apply hm
  rw [hc]
  exact dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _

theorem active_if_zero_degree (π : O) (P k : ℕ) (i : Columns H π P k)
    (h : (∑ a : H, α P k i.val a)=0) :
    (α P k i.val)=0 ∧ i.val.2.val=0 := by
  have hα : (α P k i.val)=0 := by
    funext e
    have h₁ : α P k i.val e≤ ∑ a : H, α P k i.val a :=
      Finset.single_le_sum (f:=α P k i.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    exact Nat.eq_zero_of_le_zero (h ▸ h₁)
  refine ⟨hα,?_⟩
  by_contra hj
  obtain ⟨m,hm⟩ := i.property
  apply hm
  have hzero : symCol π P k i.val=0 := by
    unfold symCol
    rw [h,if_pos (Nat.zero_le _),hα]
    simp [feature,rawFeature,Polynomial.coeff_one,hj]
  rw [hzero,MvPolynomial.coeff_zero]
  exact dvd_zero _

abbrev J5Shell (H : Type*) (P k : ℕ) :=
  Unit ⊕ (Σ e : Fin (DegreeCap P k),
    Sym H (e.val+1) × Fin (k-(e.val+2-P)))

def unpackShell (P k : ℕ) (hk : 0<k) : J5Shell H P k → Box H P k
  | .inl _ => (fun _ => ⟨0,Nat.zero_lt_succ _⟩,⟨0,hk⟩)
  | .inr ⟨e,m,j⟩ =>
    (fun i => ⟨(m:Multiset H).count i,by
      have hc : (m:Multiset H).count i≤(m:Multiset H).card := Multiset.count_le_card _ _
      have hM : (m:Multiset H).card=e.val+1 := m.property
      have he := e.isLt
      omega⟩,
      ⟨j.val+(e.val+2-P),by have hj := j.isLt; omega⟩)

theorem column_in_shell (π : O) (P k : ℕ) (hk : 0<k) (i : Columns H π P k) :
    ∃ x : J5Shell H P k, unpackShell P k hk x=i.val := by
  obtain ⟨hd,hl⟩ := active_degree_cut π P k i
  let d := ∑ a : H, α P k i.val a
  change d≤DegreeCap P k at hd
  change d+1-P≤ i.val.2.val at hl
  by_cases hz : d=0
  · obtain ⟨ha,hj⟩ := active_if_zero_degree π P k i hz
    refine ⟨.inl (),Prod.ext ?_ ?_⟩
    · funext u
      apply Fin.ext
      exact (congrFun ha u).symm
    · exact Fin.ext hj.symm
  · let l : Fin (DegreeCap P k) := ⟨d-1,by omega⟩
    let f : H →₀ ℕ := Finsupp.equivFunOnFinite.symm (α P k i.val)
    have hL : l.val+1=d := by dsimp [l]; omega
    have hC : (f.toMultiset).card=l.val+1 := by
      rw [Finsupp.card_toMultiset,Finsupp.sum_fintype]
      · simp only [f,Finsupp.equivFunOnFinite_symm_apply_toFun,id_eq]
        exact hL.symm
      · intro _
        rfl
    let m : Sym H (l.val+1) := ⟨f.toMultiset,hC⟩
    have hoff : l.val+2-P≤ i.val.2.val := by
      have hh : l.val+2=d+1 := by omega
      rwa [hh]
    let j : Fin (k-(l.val+2-P)) := ⟨i.val.2.val-(l.val+2-P),by
      have hi := i.val.2.isLt
      omega⟩
    refine ⟨.inr ⟨l,m,j⟩,Prod.ext ?_ ?_⟩
    · funext h
      apply Fin.ext
      change (f.toMultiset).count h=α P k i.val h
      rw [Finsupp.count_toMultiset]
      rfl
    · apply Fin.ext
      change (i.val.2.val-(l.val+2-P))+(l.val+2-P)=i.val.2.val
      exact Nat.sub_add_cancel hoff

theorem J5_bound (π : O) (P k : ℕ) (hk : 0<k) :
    Fintype.card (Columns H π P k)≤
      1+∑ e : Fin (DegreeCap P k),
        (Fintype.card H+e.val).choose (e.val+1) * (k-(e.val+2-P)) := by
  choose w hw using (fun i : Columns H π P k => column_in_shell π P k hk i)
  have hInj : Function.Injective w := by
    intro i j h
    apply Subtype.ext
    rw [← hw i,← hw j,h]
  apply (Fintype.card_le_of_injective w hInj).trans
  rw [Fintype.card_sum,Fintype.card_sigma]
  simp only [Fintype.card_unit,Fintype.card_prod,Fintype.card_fin,Sym.card_sym_eq_choose]
  exact le_rfl

#print axioms active_degree_cut
#print axioms active_if_zero_degree
#print axioms column_in_shell
#print axioms J5_bound
end
end V8CapacitySpecialJ5

