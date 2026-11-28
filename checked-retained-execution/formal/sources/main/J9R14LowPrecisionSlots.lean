import J9R14LowPrecisionGeometry
import J9R14LowPrecisionTiedCube
import J9R14LowPrecisionKernel

/-!
# P5--P7 on complete native linear-column slots

We sum real column ports with their original equality factors.
Every unselected leg is an affine function of the same-packet Cauchy
row. In a selected leg the only private column dependence is one source
moment; its kernel is public. A feasible allocation pays once per
selected occurrence (including repeated modes).
-/

namespace J9R14LowPrecisionSlots
open scoped Polynomial BigOperators Classical
open Polynomial DenominatorBudget PrecisionErasure OuterNodePacking
open J9R14LowPrecisionGeometry J9R14LowPrecisionLinear
open J9R14LowPrecisionColumn J9R14LowPrecisionTiedCube

noncomputable section

variable {P V R Q A M : Type*} {L : ℕ}
variable [Fintype P] [Fintype R] [Fintype Q]

variable (layout : Seats P R Q L) (old : Finset V) (owner : Slot P L→V) (t : ℤ)

abbrev FreeOwner := ↥(kept layout old owner t)

def protectedOwner : Q→Option (FreeOwner layout old owner t) := fun q =>
  if h : owner (layout.col q)∈kept layout old owner t then some ⟨owner (layout.col q),h⟩ else none

set_option linter.unusedSectionVars false in
theorem protected_some (q : Q) (u : FreeOwner layout old owner t)
    (h : protectedOwner layout old owner t q=some u) :
    owner (layout.col q)∈kept layout old owner t := by
  unfold protectedOwner at h
  split at h
  · assumption
  · contradiction

def leg (a : ℕ) (take : R→Q→Prop) (kernel : R→M→TwoLocal[X]) (moment : M→Q→TwoLocal)
    (bits : R→Bool) (α : R→Option M) (r : R) (x : Q→Bool) : TwoLocal[X] :=
  match α r with
  | none => LiteralPortCompiler.affine (bits r)
      (∑ q : Q, coeffEntry layout a t take r q * bitC (x q))
  | some m => (C (LiteralPortCompiler.slope (R:=TwoLocal) (bits r))*kernel r m) *
      ∑ q : Q, C (moment m q)*bitC (x q)

def fallback (a : ℕ) (take : R→Q→Prop) (kernel : R→M→TwoLocal[X]) (moment : M→Q→TwoLocal)
    (bits : R→Bool) (α : R→Option M)
    (rest : Rest (protectedOwner layout old owner t)→Bool) (r : R) : Linear (FreeOwner layout old owner t) TwoLocal :=
  let p := protectedOwner layout old owner t
  let x := unlift p rest
  match α r with
  | none => affine (bits r) (lin p x (coeffEntry layout a t take r))
  | some m => scale (C (LiteralPortCompiler.slope (R:=TwoLocal) (bits r))*kernel r m)
      (lin p x (fun q => C (moment m q)))

def allowance (α : R→Option M) (r : R) : ℕ := if (α r).isSome then 1 else 0

theorem fallback_exact (a : ℕ) (take : R→Q→Prop) (kernel : R→M→TwoLocal[X])
    (moment : M→Q→TwoLocal) (bits : R→Bool) (α : R→Option M)
    (rest : Rest (protectedOwner layout old owner t)→Bool) (r : R) (x : Finset (FreeOwner layout old owner t)) :
    (fallback layout old owner t a take kernel moment bits α rest r).value x =
      leg layout t a take kernel moment bits α r
        (columnBits (protectedOwner layout old owner t) (unlift (protectedOwner layout old owner t) rest) x) := by
  cases h : α r <;> simp [fallback,leg,h,affine_exact,lin_exact,scale_exact]

theorem fallback_unselected (a : ℕ) (take : R→Q→Prop) (kernel : R→M→TwoLocal[X])
    (moment : M→Q→TwoLocal) (bits : R→Bool) (α : R→Option M)
    (rest : Rest (protectedOwner layout old owner t)→Bool) (r : R) (h : allowance α r=0)
    (u : FreeOwner layout old owner t) :
    ((fallback layout old owner t a take kernel moment bits α rest r).byBit u).coeff 0=0 := by
  cases ha : α r with
  | none =>
    simp only [fallback,ha]
    apply affine_constant_zero
    intro u
    apply lin_constant_zero
    intro q v hv
    exact untouched_constant_zero layout a t old owner take r q (protected_some layout old owner t q v hv)
  | some m => simp [allowance,ha] at h

def assignmentSlot (a : ℕ) (take : R→Q→Prop) (kernel : R→M→TwoLocal[X]) (moment : M→Q→TwoLocal)
    (bits : R→Bool) (α : R→Option M) (w : (Rest (protectedOwner layout old owner t)→Bool)→TwoLocal) :
    TwoLocal[X] :=
  ∑ x : Q→Bool, guardWeight (protectedOwner layout old owner t) x *
    C (w (restrict (protectedOwner layout old owner t) x)) * ∏ r : R, leg layout t a take kernel moment bits α r x

theorem coefficients_from_original_cube
    (a : ℕ) (take : R→Q→Prop) (kernel : R→M→TwoLocal[X]) (moment : M→Q→TwoLocal)
    (bits : R→Bool) (α : R→Option M) (w : (Rest (protectedOwner layout old owner t)→Bool)→TwoLocal)
    (hOwn : ∀ u, ∃ q, protectedOwner layout old owner t q=some u)
    (k : ℕ) (hk : (∑ r : R,allowance α r)≤k) (j : ℕ) :
    (2:TwoLocal)^((kept layout old owner t).card-k-j) ∣
      (assignmentSlot layout old owner t a take kernel moment bits α w).coeff j := by
  rw [assignmentSlot,original_sum_tied _ hOwn (fun y => C (w y))
    (fun x => ∏ r : R, leg layout t a take kernel moment bits α r x)]
  have hc : Fintype.card (FreeOwner layout old owner t)=(kept layout old owner t).card := Fintype.card_coe _
  rw [← hc]
  refine coeff_budget_sum _ _ _ _ (fun y _ l => ?_) j
  rw [Polynomial.coeff_C_mul]
  simp_rw [← fallback_exact layout old owner t a take kernel moment bits α y]
  exact dvd_mul_of_dvd_right
    (coeff_linear_product (fallback layout old owner t a take kernel moment bits α y) (allowance α)
      k l hk (fallback_unselected layout old owner t a take kernel moment bits α y)) _

set_option linter.unusedSectionVars false in
theorem allowance_count [Fintype M] (α : R→Option M) :
    (∑ r : R, allowance α r) =
      ∑ m : M, (∑ r : R, LiteralPortCompiler.exponent (α r)) m := by
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  cases h : α r <;> simp [allowance,LiteralPortCompiler.exponent,h,Finsupp.single_apply]

/-- This constructs the exact exponent premise previously called
hCoeff, for arbitrary finite feasible menus and all sign/table choices.
The weight is the remaining original column/table weight after
fixing the non-protected incidences. -/
theorem menu_coefficients [Fintype M] (a : ℕ) (take : R→Q→Prop)
    (kernel : R→M→TwoLocal[X]) (moment : M→Q→TwoLocal)
    (ticket : Finset A) (bits : A→R→Bool) (α : A→R→Option M)
    (w : A→(Rest (protectedOwner layout old owner t)→Bool)→TwoLocal)
    (hOwn : ∀ u, ∃ q, protectedOwner layout old owner t q=some u)
    (β : M→₀ℕ)
    (hβ : ∀ c∈ticket, (∑ r : R, LiteralPortCompiler.exponent (α c r))=β)
    (j : ℕ) :
    (2:TwoLocal)^((kept layout old owner t).card-(∑ m : M,β m)-j) ∣
      (∑ c∈ticket, assignmentSlot layout old owner t a take kernel moment (bits c) (α c) (w c)).coeff j := by
  apply coeff_budget_sum
  intro c hc l
  apply coefficients_from_original_cube layout old owner t a take kernel moment (bits c) (α c) (w c) hOwn
  rw [allowance_count,hβ c hc]

/-- P7 for every integral probe. It is vital that the source moments
are linear port sums and the selected kernels are public. -/
theorem every_legal_probe_zero [Fintype M] {K : Type*} [CommRing K] (ψ : TwoLocal→+*K) (z : K)
    (a p : ℕ) (take : R→Q→Prop) (kernel : R→M→TwoLocal[X]) (moment : M→Q→TwoLocal)
    (ticket : Finset A) (bits : A→R→Bool) (α : A→R→Option M)
    (w : A→(Rest (protectedOwner layout old owner t)→Bool)→TwoLocal)
    (hOwn : ∀ u, ∃ q, protectedOwner layout old owner t q=some u)
    (β : M→₀ℕ)
    (hβ : ∀ c∈ticket, (∑ r : R, LiteralPortCompiler.exponent (α c r))=β)
    (v : ℕ) (hV : (∑ m : M, β m)≤v)
    (hprec : p≤(kept layout old owner t).card) (hnil : (2:K)^p=0) :
    (2:K)^v*z^(∑ m : M,β m)*
      (∑ c∈ticket, assignmentSlot layout old owner t a take kernel moment (bits c) (α c) (w c)).eval₂ ψ (2*z)=0 := by
  have he := every_slot_erased ψ _ z (kept layout old owner t).card (∑ m : M,β m) v hV
    (menu_coefficients layout old owner t a take kernel moment ticket bits α w hOwn β hβ)
  have h := (pow_dvd_pow (2:K) hprec).trans he
  rwa [hnil,zero_dvd_iff] at h

#print axioms coefficients_from_original_cube
#print axioms allowance_count
#print axioms menu_coefficients
#print axioms every_legal_probe_zero

end
end J9R14LowPrecisionSlots
