import J5R41LiteralChildCostTariff

/-! Row sweep, initialization and genuinely branched binary powering
are charged separately from the column gather. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

variable {R : Type*} [Monoid R]

def chargedPower (x : R) : List Bool → R → R × ℕ
  | [],acc => (acc,0)
  | b::bs,acc =>
     if b then
       let out := chargedPower x bs ((acc*acc)*x)
       (out.1,2+out.2)
     else
       let out := chargedPower x bs (acc*acc)
       (out.1,1+out.2)

theorem chargedPower_exact (x : R) (xs : List Bool) (acc : R) :
    chargedPower x xs acc =
      (J45Cost.digitPower x xs acc,J45Cost.digitMultiplications xs) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [chargedPower,J45Cost.digitPower,J45Cost.digitMultiplications,ih]

theorem native_branched_power (x : R) (n : ℕ) :
    (chargedPower x n.bits.reverse 1).1=x^n ∧
    (chargedPower x n.bits.reverse 1).2≤2*n := by
  rw [chargedPower_exact]
  exact ⟨native_digit_power x n,
    (J45Cost.digitMultiplications_le _).trans (Nat.mul_le_mul_left _ (canonical_digits_len n))⟩

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G)

abbrev ActualRowMultiplications (t : ℤ) :=
  (↥(matched P i g t)→Bool) × J45Cost.RowMultiply (RowPort P i g)

theorem row_reduction_exact_visits (t : ℤ) :
    Nat.card (ActualRowMultiplications P i g t) =
      2^(matched P i g t).card*
        ∑ b : RowVertex P i g,2^Fintype.card (RowPort P i g b)*(Fintype.card (RowPort P i g b)+1) := by
  unfold ActualRowMultiplications J45Cost.RowMultiply
  rw [Nat.card_prod,Nat.card_fun,Nat.card_eq_fintype_card (α:=Bool),Fintype.card_bool,
    Nat.card_eq_fintype_card (α:=↥(matched P i g t)),Fintype.card_coe,Nat.card_eq_fintype_card,Fintype.card_sigma]
  congr 1
  refine Finset.sum_congr rfl fun b _=>?_
  rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_option]

theorem row_reduction_bounded_degree (t : ℤ) (d : ℕ)
    (h : ∀ b : A,Nat.card (ParentPorts N (.inl b))≤d) :
    Nat.card (ActualRowMultiplications P i g t)≤
      2^(matched P i g t).card*(Fintype.card A*(2^d*(d+1))) := by
  rw [row_reduction_exact_visits]
  apply Nat.mul_le_mul_left
  let U := RowVertex P i g
  have hd (b : U) : Fintype.card (RowPort P i g b)≤d := by
    rw [←Nat.card_eq_fintype_card,Nat.card_congr (rowPortsEquiv N b.val)]
    exact h b.val
  calc
    _≤∑ _ : U,2^d*(d+1) := by
      refine Finset.sum_le_sum fun b _=>?_
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (hd b)) (Nat.succ_le_succ (hd b))
    _=Fintype.card U*(2^d*(d+1)) := by simp
    _≤_ := Nat.mul_le_mul_right _ (Fintype.card_le_of_injective _ Subtype.val_injective)

#print axioms chargedPower_exact
#print axioms native_branched_power
#print axioms row_reduction_exact_visits
#print axioms row_reduction_bounded_degree
end
end J5R41LiteralChildCost

