import V8PooledMenuRoot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1350000
set_option maxRecDepth 2000

namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial V8PooledMenu.FiveCopy
noncomputable section

/-- Any two different prescribed bit words are valid separated probes,
not only the special enumerator chosen inside the verification. -/
theorem actual_binary_lifts_separated (d : ℕ) (hp : 0<d) (f : ℤ[X])
    (hf : f.Monic) (hd : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (x y : Fin f.natDegree → Bool) (hxy : x≠y) :
    IsUnit (NativeProbeRing.probe d f y - NativeProbeRing.probe d f x) := by
  apply NativeProbeRing.unit_of_residue d hp f hf
  rw [map_sub,sub_ne_zero]
  intro e
  exact hxy (NativeProbeRing.binary_residues_injective d hp f hf hd e.symm)

theorem actual_roster_words_separated {V : Type} [Fintype V] {f : ℤ[X]}
    (d : ℕ) (hp : 0<d) (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (W : Probes V f) (t : Site V) (j j' : Fin (probeCount V)) (h : j≠j') :
    IsUnit (NativeProbeRing.probe d f (W.word t j') - NativeProbeRing.probe d f (W.word t j)) :=
  actual_binary_lifts_separated d hp f hf hd _ _ (fun h' => h (W.distinct t h'))

theorem actual_box_binary_lifts_separated (d : ℕ) (hp : 0<d) (f : ℤ[X])
    (hf : f.Monic) (hd : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (x y : Fin f.natDegree → Bool) (hxy : x≠y) :
    IsUnit (readProbe f d y - readProbe f d x) := by
  unfold readProbe
  rw [←map_sub]
  exact (actual_binary_lifts_separated d hp f hf hd x y hxy).map
    (J6ActiveInterpolation.scalarIn d f 1)

#print axioms actual_binary_lifts_separated
#print axioms actual_roster_words_separated
#print axioms actual_box_binary_lifts_separated
end

end V8R45PooledLiteral