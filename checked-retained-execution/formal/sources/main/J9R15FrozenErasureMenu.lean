import J9R15FrozenErasureFactors
import J9R15FrozenErasureGeneric

/-! P7 on the actual physically compiled children of the identical
J7 same-seat original EntryFile. The high-precision mode alphabet is
not replaced with the receiver's lower-precision alphabet. -/
namespace J9R15FrozenErasure
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral J6R10Integral
open J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout J6R14SpecializedBox
open J9R14LowPrecisionGeometry J9R14LowPrecisionSlots J9R14LowPrecisionTiedCube
open J9R14LowPrecisionNative J9R14LowPrecisionComplete J9R14LowPrecisionMenu
open J9R15FrozenErasurePhysical J9R15FrozenErasureProjection J6R9PacketScopes

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 2500
set_option linter.unusedSectionVars false

variable {A Pair Row Col W : Type} [LinearOrder A]
variable [Fintype A] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t b : ℕ}
variable (row : W → Row) (col : W → OrdinaryColumn Pair Col)
variable (two : ∀ r, Nat.card {w : W // row w=r}=2) (state : DState A Pair Row Col t)
variable (seat : Wire Pair W ↪ Physical (t+1) b A)
variable (preserve : ∀ w, physicalCell (J7SeatPacking.balancedMask (t+1) b) (seat w)
  = wordLabel row col state w)
variable (budget : Nat.card (Page (t+1) b A)*2^(t+1) ≤ 3*Nat.card (Wire Pair W))

local notation "E" => Wire Pair W
local notation "P" => J7R13.asPacking row col state seat preserve budget
local notation "D" => physicalLayout row col two state seat preserve
local notation "MASK" => (J7SeatPacking.balancedMask (K:=A) (t+1) b)
local notation "ρ" => (fun e : E => seat e)
local notation "D'" => nativeSeats ρ ρ
local notation "old" => cloneHosts (Pair:=Pair) (Col:=Col)
local notation "OWN" => seatOwner col seat
variable {n : ℤ}
local notation "K" => kept D' old OWN n
local notation "PR" => protectedOwner D' old OWN n

/-- Every tuple of the high-precision alphabet erases in a low-precision
receiver. The input is the actual product of the retained and newly
created child files on the same J7 seat, not a presumed completed equality. -/
theorem native_outer_erasure_after
    (F : J8Physical.OldTables D) (hF : CloneTruth row col two state seat preserve F)
    (sign : Pin Pair → Bool) (f : ℤ[X]) (ell p₀ : ℕ)
    (hf : f.Monic) (hp₀ : 0<p₀) (hd : 0<f.natDegree) (hℓ : 0<ell)
    (i : Fin (t+1)) (hn : n≠0) (hv : padicValInt 2 n=i.val) (p : ℕ) (z : Box f ell p)
    {R : Type*} [CommRing R] (σ : Box f ell p →+* R)
    (q : ℕ) (hNil : (2:R)^q=0) (hprec : q≤(K).card) (β : Mode i p MASK →₀ ℕ) :
    let file := sameSeatFile row col two state seat preserve f ell p₀ F sign
    σ (actualProjection P i hn hv p z file hf β)=0 := by
  let file := sameSeatFile row col two state seat preserve f ell p₀ F sign
  let wt := restWeight row col two state seat preserve (n:=n) F sign
  let packing := J7R13.asPacking row col state seat preserve budget
  have fac := frozen_factors row col two state seat preserve (n:=n) F hF sign f ell p₀ p hf hp₀ hd hℓ
  exact J9R15FrozenErasureGeneric.projected_zero packing i hn hv p z file hf old OWN wt fac
    σ (clonePorts_supply col seat) q hNil hprec β

def outer (t : ℕ) : ℤ := ((2^(t+1):ℕ):ℤ)-1

theorem outer_odd (t : ℕ) : Odd (outer t) := by
  refine ⟨(2:ℤ)^t-1,?_⟩
  unfold outer
  rw [Int.natCast_pow]
  change (2:ℤ)^(t+1)-1 = _
  rw [pow_succ]
  ring

theorem outer_nonzero (t : ℕ) : outer t≠0 := by
  intro hz
  have h := outer_odd t
  rw [hz] at h
  exact (by decide : ¬Odd (0:ℤ)) h

def outerIdx (t : ℕ) : Fin (t+1) := ⟨0,Nat.zero_lt_succ t⟩

theorem outer_val (t : ℕ) : padicValInt 2 (outer t)=(outerIdx t).val :=
  P1DyadicGrid.odd_valuation_zero (outer_odd t)

include budget in
theorem four_clone_untouched (N : ℕ) (hPair : Fintype.card Pair=2*N)
    (hEdges : Fintype.card E=24*N) :
    (24*(N:ℚ))/6-3*(24*(N:ℚ))/(2^(t+1):ℕ) ≤
      ((kept D' old OWN (outer t)).card:ℚ) := by
  have hcap : Fintype.card (Page (t+1) b A)*2^(t+1)≤3*(24*N) := by
    simpa only [Nat.card_eq_fintype_card,hEdges] using budget
  have hc : (old).card=4*N := by
    rw [cloneHosts_card,hPair]
    omega
  letI : DecidableEq (Option (Pin Pair ⊕ OrdinaryColumn Pair Col)) := Classical.decEq _
  letI : DecidableEq (Page (t+1) b A) := Classical.decEq _
  simpa only [kept,outer] using OuterNodePacking.j9_four_clone Finset.univ (rowReal D') (colReal D') old OWN N
    (by positivity) hc (by simpa only [Finset.card_univ] using hcap)

#print axioms native_outer_erasure_after
#print axioms outer_odd
#print axioms outer_nonzero
#print axioms outer_val
#print axioms four_clone_untouched
end
end J9R15FrozenErasure
