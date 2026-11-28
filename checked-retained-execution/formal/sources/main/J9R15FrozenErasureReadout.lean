import J9R15FrozenErasureMenu
import J9R15FrozenErasurePrecision

/-! The actual completed values of the high menu, read modulo 2^q without
regenerating either the fixed high β or any child EntryFile. -/
namespace J9R15FrozenErasure
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral J6R10Integral
open J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout J6R14SpecializedBox
open J9R15FrozenErasurePhysical J9R15FrozenErasurePrecision J6R9PacketScopes

noncomputable section
set_option maxHeartbeats 1200000
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
local notation "I" => outerIdx t
local notation "ht" => outer_nonzero t
local notation "hv" => outer_val t

/-- The unchanged arbitrary-syntax file, with a certificate on each original
clone's own literal port truth table only. Complete native slots vanish at
every high probe, every sign, and every high-menu request β. -/
theorem four_clone_same_file_low_bits
    (F : J8Physical.OldTables D) (hF : CloneTruth row col two state seat preserve F)
    (f : ℤ[X]) (ell p₀ : ℕ) (hf : f.Monic) (hp₀ : 0<p₀) (hd : 0<f.natDegree) (hℓ : 0<ell)
    (N : ℕ) (hPair : Fintype.card Pair=2*N) (hEdges : Fintype.card E=24*N)
    (p q : ℕ) (hqp : q≤p)
    (hq : (q:ℚ)≤(24*(N:ℚ))/6-3*(24*(N:ℚ))/(2^(t+1):ℕ))
    (z : Box f ell p) (β : Mode I p MASK →₀ ℕ) (sign : Pin Pair → Bool) :
    let file := sameSeatFile row col two state seat preserve f ell p₀ F sign
    (∏ g : A, reduce q f ell (actualChildTruth P I ht hv p z file hf β g))=0 := by
  dsimp only
  rw [← lower_actual_product P I ht hv p q hqp z]
  exact native_outer_erasure_after row col two state seat preserve budget F hF sign f ell p₀ hf hp₀ hd hℓ
    I ht hv p z (lowerBox p q hqp f ell) q (box_two_nil q f ell)
    (by exact_mod_cast hq.trans (four_clone_untouched col seat budget N hPair hEdges)) β

/-- Explicit original clone CNFs. The old ordinary clauses, sign pins,
orientation, binary address, high-precision tuple, packet children, and
creation tags have not changed. -/
theorem four_clone_frozen_binary_menu
    (F : J8Physical.OldTables D) (f : ℤ[X]) (ell p₀ : ℕ)
    (hf : f.Monic) (hp₀ : 0<p₀) (hd : 0<f.natDegree) (hℓ : 0<ell)
    (N : ℕ) (hPair : Fintype.card Pair=2*N) (hEdges : Fintype.card E=24*N)
    (p q : ℕ) (hqp : q≤p)
    (hq : (q:ℚ)≤(24*(N:ℚ))/6-3*(24*(N:ℚ))/(2^(t+1):ℕ))
    (addr : Fin f.natDegree → Bool) (β : Mode I p MASK →₀ ℕ) (sign : Pin Pair → Bool) :
    let z := J6ActiveInterpolation.scalarIn p f ell (NativeProbeRing.probe p f addr)
    let file := sameSeatFile row col two state seat preserve f ell p₀
      (canonicalOld row col two state seat preserve F) sign
    (∏ g : A, reduce q f ell (actualChildTruth P I ht hv p z file hf β g))=0 := by
  exact four_clone_same_file_low_bits row col two state seat preserve budget
    (canonicalOld row col two state seat preserve F)
    (canonical_clone_truth row col two state seat preserve F) f ell p₀ hf hp₀ hd hℓ
    N hPair hEdges p q hqp hq _ β sign

#print axioms four_clone_same_file_low_bits
#print axioms four_clone_frozen_binary_menu
end
end J9R15FrozenErasure
