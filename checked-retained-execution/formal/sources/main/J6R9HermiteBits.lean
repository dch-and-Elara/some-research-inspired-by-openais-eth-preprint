import J6R9HermiteNative

/-! Turning the actual residue into a count (and hence every bit) when
the independently certified range fits the selected precision. -/
namespace J6R9Hermite
open DyadicProbeCompiler NativeProbeRing J6ActiveSchedule

theorem natural_count_from_native (p : ℕ) (z out : Source) (n : ℕ)
    (hres : coeffReduction p z=coeffReduction p out)
    (exactCount : J8EndToEnd.rationalMap out=(n:ℚ))
    (fits : n<(2:ℕ)^p) :
    (coeffReduction p z).val=n := by
  haveI : NeZero ((2:ℕ)^p) := ⟨pow_ne_zero _ (by decide)⟩
  have he : out=(n:Source) := by
    apply J8EndToEnd.rationalMap_injective
    simpa only [map_natCast] using exactCount
  rw [hres,he,map_natCast]
  exact ZMod.val_natCast_of_lt fits

theorem finite_native_count (a M u p : ℕ) (hM : u≤M)
    (truth : ℤ→ℕ→Source) (out : Source)
    (menu : (t : ℤ)→ℕ→Base (childPrecision p a M u t))
    (correct : recompose a M u (fun t j => J8EndToEnd.rationalMap (truth t j)) =
      J8EndToEnd.rationalMap out)
    (receipt : ∀ t∈active a M u, ∀ j<order M u t,
      menu t j=coeffReduction (childPrecision p a M u t) (truth t j))
    (n : ℕ) (exactCount : J8EndToEnd.rationalMap out=(n:ℚ)) (fits : n<(2:ℕ)^p) :
    ∃ z : Source, J8EndToEnd.rationalMap z =
       recompose a M u (fun t j => ((menu t j).val:ℚ)) ∧
       (coeffReduction p z).val=n ∧
       ∀ bit : ℕ, (coeffReduction p z).val.testBit bit = n.testBit bit := by
  obtain ⟨z,hz,hres⟩ := finite_native_receive a M u p hM truth out menu correct receipt
  have hn := natural_count_from_native p z out n hres exactCount fits
  exact ⟨z,hz,hn,fun j=>congrArg (fun n=>n.testBit j) hn⟩

#print axioms natural_count_from_native
#print axioms finite_native_count
end J6R9Hermite

