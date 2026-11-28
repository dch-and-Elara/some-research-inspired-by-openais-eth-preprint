import V8NativeMessageC3Canonical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3300000

/-! Whole-slot lifting now at the actual five-copy high addresses.
The losses of any two selected linear readout coefficients remain
explicit budgets, not inferred from their nominal precision. -/
namespace V8NativeMessage.C3.Canonical
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Integral J6R10Repack
open V8PooledMenu V8PooledMenu.FiveCopy V8PooledRange V8PooledRange.NativeOrigin
open V8NativeMessage.Five
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {r : ThreePorts G} {f : ℤ[X]}

def atRoot (P : Packing G r) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (t : Site V) (probes : Probes V f) (hf : f.Monic) (s : V→Bool)
    (q : Address P hu huM t) (g : Fin 64) : Residue f 1 (high t) :=
  highChildRaw P (rootIndex hu huM t) (nonzero_site hu huM t) (rootIndex_val hu huM t)
    (high t) (box_two_nil (high t) f 1)
    (readProbe f (high t) (probes.word t q.probeIdx)) (file f G r s) hf q.beta g

def wholeHigh (P : Packing G r) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (t : Site V) (probes : Probes V f) (hf : f.Monic) (s : V→Bool)
    (q : Address P hu huM t) : Residue f 1 (high t) :=
  slot P (rootIndex hu huM t) (nonzero_site hu huM t) (rootIndex_val hu huM t)
    (high t) (box_two_nil (high t) f 1)
    (readProbe f (high t) (probes.word t q.probeIdx)) (file f G r s) hf q.beta

theorem wholeHigh_is_product (P : Packing G r) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (t : Site V) (probes : Probes V f) (hf : f.Monic) (s : V→Bool)
    (q : Address P hu huM t) :
    wholeHigh P hu huM t probes hf s q=∏ g, atRoot P hu huM t probes hf s q g := rfl

def nodeD (t : Site V) : ℕ := 2^rootA V / 2^(padicValInt 2 t.val)
def printedH (V : Type) [Fintype V] : ℕ := J6ActiveSchedule.height (wireSize V) (rootU V)

theorem native_node_reserve_lower (hu : 0<rootU V) (huM : rootU V≤wireSize V) (t : Site V) :
    2^(rootU V+1)≤nodeD t := by
  have h : padicValInt 2 t.val < rootU V := (level hu huM t).isLt
  have h₁ : padicValInt 2 t.val≤rootA V := by unfold rootA; omega
  rw [nodeD,dyadic_div_pow h₁]
  apply Nat.pow_le_pow_right (by decide)
  unfold rootA
  omega

def ordinaryDLoss (t : Site V) : ℕ :=
  6*(printedH V*nodeD t) + 4*(wireSize V*(rootA V+1))

/-- Exact finite margin of the printed high precision p_t after the
declared ordinary D loss; a concrete MAIN bound must fit the margin. -/
theorem printed_fit (t : Site V) (mainLoss : ℕ)
    (hm : mainLoss ≤ 2*(printedH V*nodeD t)+4*(wireSize V*(rootA V+1))) :
    rootPrec V+(ordinaryDLoss t+mainLoss)≤high t := by
  unfold ordinaryDLoss printedH nodeD high J6ActiveSchedule.childPrecision J9PrintedSchedule.precision at *
  simp only [Nat.mul_assoc] at *
  omega

theorem C3_actual_canonical_replacement (P : Packing G r) (hu : 0<rootU V)
    (huM : rootU V≤wireSize V) (t : Site V) (probes : Probes V f)
    (hf : f.Monic) (s : V→Bool) (q : Address P hu huM t)
    (separate : Fin 64→IntRing f 1)
    (hs : ∀ g, reduce (high t) f 1 (separate g)=atRoot P hu huM t probes hf s q g)
    (mainMult dMult : RatRing f 1) {mainLoss : ℕ}
    (hm : HasLoss f 1 mainLoss mainMult) (hd : HasLoss f 1 (ordinaryDLoss t) dMult)
    (fit : mainLoss ≤ 2*(printedH V*nodeD t)+4*(wireSize V*(rootA V+1))) :
    ∃ e : IntRing f 1, (dMult*mainMult)*
      (embed f 1 (canonicalLift (high t) f hf 1 (wholeHigh P hu huM t probes hf s q)) -
        embed f 1 (∏ g, separate g)) =
      embed f 1 ((2:IntRing f 1)^rootPrec V*e) := by
  rw [wholeHigh_is_product]
  exact actual_separate_transfer (high t) f hf 1 (rootPrec V)
    (atRoot P hu huM t probes hf s q) separate hs (dMult*mainMult)
    (loss_suffices (loss_mul hd hm) (printed_fit t mainLoss fit))

#print axioms wholeHigh_is_product
#print axioms native_node_reserve_lower
#print axioms printed_fit
#print axioms C3_actual_canonical_replacement
end
end V8NativeMessage.C3.Canonical