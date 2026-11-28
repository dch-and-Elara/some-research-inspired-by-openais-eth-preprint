import V8CapacityUnifiedScalarS5Count

/-! Exact printed S5 specialization: quotient/remainder at base q;
all such codes occur whenever the upper budget is below q. -/
namespace V8CapacityUnified.Scalar
open scoped Classical BigOperators
open V8CapacityFactorial

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem debt_under_square (q n : ℕ) (hq : 2≤q) (hn : n<q^2) :
    debt q n=n/q := by
  unfold debt
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (show 0<n+1 by omega))]
  · simp
  · intro j _ hj
    have hq' : 0<q := by omega
    exact Nat.div_eq_of_lt (hn.trans_le (Nat.pow_le_pow_right hq' (by omega)))

abbrev ResidueIndex (q L : ℕ) :=
  S2Index q (L+1) (0 : H → ℕ)

abbrev DigitTuple (q L : ℕ) :=
  (H → Fin q) × Quotas H L

theorem quotient_sum {q L : ℕ} (a : ResidueIndex (H:=H) q L) :
    (∑ i : H, indexDegree a i/q)≤L := by
  have h : weight q (0:H→ℕ) (indexDegree a)<L+1 := a.property
  apply Nat.le_of_lt_succ ((Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => div_le_debt q (indexDegree a i))).trans_lt ?_)
  simpa only [weight,Pi.zero_apply,zero_mul,zero_add] using h

def digitCode (q L : ℕ) (hq : 0<q) (a : ResidueIndex (H:=H) q L) : DigitTuple (H:=H) q L :=
  (fun i => ⟨indexDegree a i%q,Nat.mod_lt _ hq⟩,
    ⟨fun i => ⟨indexDegree a i/q,Nat.lt_succ_of_le
      ((Finset.single_le_sum (f:=fun j => indexDegree a j/q) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)).trans (quotient_sum a))⟩,quotient_sum a⟩)

theorem digitCode_injective (q L : ℕ) (hq : 0<q) :
    Function.Injective (digitCode (H:=H) q L hq) := by
  intro a b h
  apply (exactS2Index q (L+1) hq (0:H→ℕ)).injective
  apply Subtype.ext
  funext i
  have h₁ : indexDegree a i%q=indexDegree b i%q :=
    congrArg (fun d : DigitTuple (H:=H) q L => (d.1 i).val) h
  have h₂ : indexDegree a i/q=indexDegree b i/q :=
    congrArg (fun d : DigitTuple (H:=H) q L => (d.2.val i).val) h
  change indexDegree a i=indexDegree b i
  calc
    _ = indexDegree a i%q + q*(indexDegree a i/q) := (Nat.mod_add_div _ _).symm
    _ = _ := by rw [h₁,h₂,Nat.mod_add_div]

theorem digitCode_surjective (q L : ℕ) (hq₂ : 2≤q) (hL : L<q) :
    Function.Surjective (digitCode (H:=H) q L (by omega)) := by
  intro d
  have hq : 0<q := by omega
  let n (i : H) := (d.1 i).val+q*(d.2.val i).val
  have hnq (i : H) : n i/q=(d.2.val i).val := by
    unfold n
    rw [Nat.add_mul_div_left _ _ hq,Nat.div_eq_of_lt (d.1 i).isLt,zero_add]
  have hnr (i : H) : n i%q=(d.1 i).val := by
    unfold n
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (d.1 i).isLt]
  have hn (i : H) : n i<q^2 := by
    calc
      n i < q+q*(d.2.val i).val := Nat.add_lt_add_right (d.1 i).isLt _
      _ = q*((d.2.val i).val+1) := by ring
      _ ≤ q*q := Nat.mul_le_mul_left q (by have hi := (d.2.val i).isLt; omega)
      _ = q^2 := by ring
  have ha : weight q (0:H→ℕ) n<L+1 := by
    simp only [weight,Pi.zero_apply,zero_mul,zero_add]
    have hh (i : H) : debt q (n i)=(d.2.val i).val :=
      (debt_under_square q (n i) hq₂ (hn i)).trans (hnq i)
    simp only [hh]
    exact Nat.lt_succ_of_le d.2.property
  let a := indexFor q (L+1) hq (0:H→ℕ) n ha
  have he : indexDegree a=n := indexFor_degree q (L+1) hq (0:H→ℕ) n ha
  refine ⟨a,Prod.ext ?_ ?_⟩
  · funext i
    apply Fin.ext
    change indexDegree a i%q=(d.1 i).val
    rw [he,hnr]
  · apply Subtype.ext
    funext i
    apply Fin.ext
    change indexDegree a i/q=(d.2.val i).val
    rw [he,hnq]

theorem digit_tuple_card (q L : ℕ) :
    Fintype.card (DigitTuple (H:=H) q L)=
      q^(Fintype.card H)*(Fintype.card H+L).choose (Fintype.card H) := by
  rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,quota_card]

theorem S5_choose_upper (q L : ℕ) (hq : 0<q) :
    Nat.card (S2Raw q (L+1) (0:H→ℕ))≤
      q^(Fintype.card H)*(Fintype.card H+L).choose (Fintype.card H) := by
  calc
    _ = Nat.card (ResidueIndex (H:=H) q L) := (Nat.card_congr (exactS2Index q (L+1) hq (0:H→ℕ))).symm
    _ ≤ Nat.card (DigitTuple (H:=H) q L) :=
      Nat.card_le_card_of_injective (digitCode (H:=H) q L hq) (digitCode_injective q L hq)
    _ = _ := (Nat.card_eq_fintype_card).trans (digit_tuple_card (H:=H) q L)

theorem S5_choose_exact (q L : ℕ) (hq₂ : 2≤q) (hL : L<q) :
    Nat.card (S2Raw q (L+1) (0:H→ℕ))=
      q^(Fintype.card H)*(Fintype.card H+L).choose (Fintype.card H) := by
  have hq : 0<q := by omega
  calc
    _ = Nat.card (ResidueIndex (H:=H) q L) := (Nat.card_congr (exactS2Index q (L+1) hq (0:H→ℕ))).symm
    _ = Nat.card (DigitTuple (H:=H) q L) :=
      Nat.card_congr (Equiv.ofBijective _ ⟨digitCode_injective q L hq,digitCode_surjective q L hq₂ hL⟩)
    _ = _ := (Nat.card_eq_fintype_card).trans (digit_tuple_card (H:=H) q L)

theorem S5_product_upper (q L : ℕ) (hq : 0<q) :
    Nat.card (S2Raw q (L+1) (0:H→ℕ))≤(q*(L+1))^(Fintype.card H) := by
  have h : Fintype.card (Quotas H L)≤(L+1)^(Fintype.card H) := by
    simpa only [Fintype.card_fun,Fintype.card_fin] using
      (Fintype.card_le_of_injective (fun t : Quotas H L => t.val) Subtype.val_injective)
  rw [quota_card] at h
  exact (S5_choose_upper (H:=H) q L hq).trans
    ((Nat.mul_le_mul_left _ h).trans_eq (mul_pow _ _ _).symm)

theorem S5_no_loss (q : ℕ) (hq₂ : 2≤q) :
    Nat.card (S2Raw q 1 (0:H→ℕ))=q^(Fintype.card H) := by
  simpa using (S5_choose_exact (H:=H) q 0 hq₂ (by omega))

#print axioms debt_under_square
#print axioms digitCode_injective
#print axioms digitCode_surjective
#print axioms S5_choose_upper
#print axioms S5_choose_exact
#print axioms S5_product_upper
#print axioms S5_no_loss
end
end V8CapacityUnified.Scalar
