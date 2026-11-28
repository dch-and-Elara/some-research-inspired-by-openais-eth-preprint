import J9R14LowPrecisionNative

/-!
# Actual complete slots on an equality-column family

The native sum below contains actual original row-leg factors, original
equality gates, and the remaining table weight. The last weight may be
arbitrary on the other columns, but may not reuse a protected owner.
Only feasibility of the original allocation, real seats/owners and
remaining independent original tables are assumptions, not an equality
of completed coefficients or observations.
-/

namespace J9R14LowPrecisionComplete
open scoped Polynomial Classical BigOperators
open Polynomial DenominatorBudget P11FullPacking J6R9PacketScopes OuterNodePacking
open J9R14LowPrecisionSlots J9R14LowPrecisionGeometry J9R14LowPrecisionTiedCube
open J9R14LowPrecisionNative

noncomputable section

variable {S R Q A : Type*} [LinearOrder S] [Fintype R] [Fintype Q]
variable {a b : ℕ} [Fintype (Page a b S)]
variable (ρ : R→Physical a b S) (κ : Q→Physical a b S)
variable (mask : MaskFamily a b S) (i : Fin a)
variable {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
variable (old : Finset A) (owner : Slot (Page a b S) (2^a)→A)
variable {K : Type*} [CommRing K] (hnil : (2:K)^p=0) (z : K)
variable [Fintype (Mode i p mask)]

local notation "W" => Mode i p mask
local notation "D" => nativeSeats ρ κ
local notation "PROT" => protectedOwner D old owner t
local notation "ψ" => J6ZeroTransport.reduceAt p hnil

def normalizedCost (β : W →₀ ℕ) : ℕ := ∑ m : W, tariff mask i p m * β m

def slot {Y : Type*} (ticket : Finset Y)
    (bits : Y→R→Bool) (alloc : Y→R→Option W)
    (weight : Y→(Rest PROT→Bool)→TwoLocal) : K :=
  ∑ c∈ticket, ∑ x : Q→Bool,
    guardWeight PROT x * ψ (weight c (restrict PROT x)) *
      ∏ r : R, actualLeg ρ κ mask i ht hv p hnil z (bits c) x r (alloc c r)

set_option linter.unusedSectionVars false in
theorem native_cost_ge_count (β : W→₀ℕ) :
    (∑ m : W, β m) ≤ normalizedCost mask i p β := by
  unfold normalizedCost
  apply Finset.sum_le_sum
  intro m _
  have h : 1≤tariff mask i p m := by
    unfold tariff
    have := i.isLt
    omega
  simpa only [one_mul] using Nat.mul_le_mul_right (β m) h

set_option linter.unusedSectionVars false in
theorem eval_guard (g : TwoLocal[X]→+*K) (x : Q→Bool) :
    g (guardWeight PROT x)=guardWeight PROT x := by
  rw [guard_weight,guard_weight]
  split <;> simp

set_option linter.unusedSectionVars false in
theorem product_native_eval
    (α : R→Option W) (Y : R→Bool) (x : Q→Bool) (β : W→₀ℕ)
    (hβ : (∑ r : R, LiteralPortCompiler.exponent (α r))=β) :
    (∏ r : R, actualLeg ρ κ mask i ht hv p hnil z Y x r (α r)) =
      (2:K)^(normalizedCost mask i p β)*z^(∑ m : W,β m) *
        ∏ r : R, (leg D t a (take ρ κ mask i)
          (kernel ρ mask i ht hv p) (momentCoeff κ mask i p) Y α r x).eval₂ ψ (2*z) := by
  simp_rw [actual_leg_eval ρ κ mask i ht hv p hnil z Y x α]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
    Finset.prod_pow_eq_pow_sum,tariff_count mask i p α,allowance_count α,hβ]
  rfl

set_option linter.unusedSectionVars false in
theorem slot_normalized {Y : Type*} (ticket : Finset Y)
    (bits : Y→R→Bool) (alloc : Y→R→Option W)
    (weight : Y→(Rest PROT→Bool)→TwoLocal) (β : W→₀ℕ)
    (hβ : ∀ c∈ticket, (∑ r : R, LiteralPortCompiler.exponent (alloc c r))=β) :
    slot ρ κ mask i ht hv p old owner hnil z ticket bits alloc weight =
      (2:K)^(normalizedCost mask i p β)*z^(∑ m : W, β m)*
        (∑ c∈ticket, assignmentSlot D old owner t a (take ρ κ mask i)
          (kernel ρ mask i ht hv p) (momentCoeff κ mask i p) (bits c) (alloc c) (weight c)).eval₂ ψ (2*z) := by
  let E := Polynomial.eval₂RingHom ψ (2*z)
  have hE (x : Q→Bool) : E (guardWeight PROT x) = guardWeight PROT x :=
    eval_guard ρ κ (t:=t) old owner E x
  have hC (w : TwoLocal) : E (C w)=ψ w := Polynomial.eval₂_C _ _
  unfold slot assignmentSlot
  change _ = (2:K)^(normalizedCost mask i p β)*z^(∑ m : W, β m)*E _
  simp only [map_sum,map_mul,map_prod,hE,hC,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro x _
  rw [product_native_eval ρ κ mask i ht hv p hnil z _ _ _ _ (hβ c hc)]
  have hEv (q : TwoLocal[X]) : E q=q.eval₂ ψ (2*z) := rfl
  simp only [hEv]
  ring

set_option linter.unusedSectionVars false in
theorem native_slot_zero {Y : Type*} (ticket : Finset Y)
    (bits : Y→R→Bool) (alloc : Y→R→Option W)
    (weight : Y→(Rest PROT→Bool)→TwoLocal) (β : W→₀ℕ)
    (hβ : ∀ c∈ticket, (∑ r : R, LiteralPortCompiler.exponent (alloc c r))=β)
    (hOwn : ∀ u, ∃ q, PROT q=some u)
    (hprec : p≤(kept D old owner t).card) :
    slot ρ κ mask i ht hv p old owner hnil z ticket bits alloc weight=0 := by
  rw [slot_normalized ρ κ mask i ht hv p old owner hnil z ticket bits alloc weight β hβ]
  exact every_legal_probe_zero D old owner t ψ z a p (take ρ κ mask i) (kernel ρ mask i ht hv p)
    (momentCoeff κ mask i p) ticket bits alloc weight hOwn β hβ (normalizedCost mask i p β)
    (native_cost_ge_count mask i p β) hprec hnil

set_option linter.unusedSectionVars false in
/-- The numerical four-clone threshold, with no separate hCoeff
premise. It applies independently to each menu request and hence to
all sign words and all legal outer-node probes. -/
theorem four_clone_outer_slot_zero {Y : Type*} (ticket : Finset Y)
    (bits : Y→R→Bool) (alloc : Y→R→Option W)
    (weight : Y→(Rest PROT→Bool)→TwoLocal) (β : W→₀ℕ)
    (hβ : ∀ c∈ticket, (∑ r : R, LiteralPortCompiler.exponent (alloc c r))=β)
    (hOwn : ∀ u, ∃ q, PROT q=some u) (N : ℕ)
    (hOuter : t=((2^a:ℕ):ℤ)-1) (hOld : old.card=4*N)
    (hPack : Fintype.card (Page a b S) * 2^a ≤ 3*(24*N))
    (hp : (p:ℚ) ≤ (24*(N:ℚ))/6-3*(24*(N:ℚ))/(2^a:ℕ)) :
    slot ρ κ mask i ht hv p old owner hnil z ticket bits alloc weight=0 := by
  have hK : (24*(N:ℚ))/6-3*(24*(N:ℚ))/(2^a:ℕ)≤((kept D old owner t).card:ℚ) := by
    rw [hOuter]
    exact j9_four_clone Finset.univ (rowReal D) (colReal D) old owner N (by positivity) hOld
      (by simpa only [Finset.card_univ] using hPack)
  exact native_slot_zero ρ κ mask i ht hv p old owner hnil z ticket bits alloc weight β hβ hOwn
    (by exact_mod_cast hp.trans hK)

#print axioms native_cost_ge_count
#print axioms product_native_eval
#print axioms slot_normalized
#print axioms native_slot_zero
#print axioms four_clone_outer_slot_zero

end
end J9R14LowPrecisionComplete
