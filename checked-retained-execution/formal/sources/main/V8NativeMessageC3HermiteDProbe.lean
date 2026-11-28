import V8NativeMessageC3HermiteDStencil

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

/-! The tested D schedule loss and the linear finite receiver are
instantiated at the actual five-copy probe list. The field coefficient
for a raw address lifts only the public decoder-basis coefficient. -/
namespace V8NativeMessage.C3.Hermite.D
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9Recursive J6R10Integral
open V8PooledMenu V8PooledMenu.FiveCopy V8PooledRange
open Canonical
noncomputable section

private theorem binary_pair_units {f : ℤ[X]} (p : ℕ) (hp : 0<p)
    (hf : f.Monic) (hF : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (a b : Fin f.natDegree→Bool) (hab : a≠b) :
    IsUnit (J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f a) -
      J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f b)) := by
  let x : NativeProbeRing.Scalar p f := NativeProbeRing.probe p f a
  let y : NativeProbeRing.Scalar p f := NativeProbeRing.probe p f b
  let r := NativeProbeRing.residueMap p hp f
  have hne : r x≠r y := by
    intro e
    exact hab (NativeProbeRing.binary_residues_injective p hp f hf hF e)
  have hz : r (x-y)≠0 := by rw [map_sub,sub_ne_zero]; exact hne
  have hunit := NativeProbeRing.unit_of_residue p hp f hf (x-y) hz
  rw [← (J6ActiveInterpolation.scalarIn p f 1).map_sub]
  exact hunit.map (J6ActiveInterpolation.scalarIn p f 1)

variable (V : Type) [Fintype V]

def dNode {f : ℤ[X]} (p : ℕ) (t : Site V) (probes : Probes V f) (z : Fin (probeCount V)) :
    Box f 1 p :=
  readProbe f p (probes.word t z)

def unitDifferences {R I : Type} [CommRing R] (node : I→R) : Prop :=
  ∀ i j, i≠j → IsUnit (node j-node i)

theorem d_node_separation {f : ℤ[X]} (p : ℕ) (hp : 0<p)
    (t : Site V) (probes : Probes V f)
    (hf : f.Monic) (hF : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    unitDifferences (R:=Box f 1 p) (dNode V p t probes) := by
  intro i j hij
  have hwords : probes.word t j≠probes.word t i := fun e => hij ((probes.distinct t) e.symm)
  exact binary_pair_units p hp hf hF _ _ hwords

theorem d_high_pos (t : Site V) (hu : 0<rootU V) (hM : rootU V≤wireSize V) : 0<high t :=
  (Nat.zero_le (rootPrec V)).trans_lt
    (J6ActiveSchedule.child_monotone (rootPrec V) (rootA V) (wireSize V) (rootU V) t.val
      (hu.trans_le hM))

#print axioms d_node_separation
#print axioms d_high_pos
end
end V8NativeMessage.C3.Hermite.D