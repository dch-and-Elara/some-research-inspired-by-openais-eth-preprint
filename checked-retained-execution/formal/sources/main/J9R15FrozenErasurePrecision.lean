import J9R15FrozenErasurePhysical

/-! Genuine reduction through the two finite polynomial quotients, at the
same binary address. This does not change the high-precision request β. -/
namespace J9R15FrozenErasurePrecision
open scoped Polynomial
open Polynomial J6R9Recursive J6R10Integral NativeProbeRing

noncomputable section

def lowerBase (p q : ℕ) (hqp : q≤p) : Base p →+* Base q :=
  NativeProbeRing.reduceBase q p hqp

def lowerScalar (p q : ℕ) (hqp : q≤p) (f : ℤ[X]) : Scalar p f →+* Scalar q f :=
  NativeProbeRing.reduceScalar q p hqp f

def lowerBox (p q : ℕ) (hqp : q≤p) (f : ℤ[X]) (ell : ℕ) :
    Box f ell p →+* Box f ell q :=
  adjoinMap (lowerScalar p q hqp f) (X^ell) (X^ell) (by simp)

theorem lower_binary_address (p q : ℕ) (hqp : q≤p) (f : ℤ[X]) (ell : ℕ)
    (bits : Fin f.natDegree → Bool) :
    lowerBox p q hqp f ell (J6ActiveInterpolation.scalarIn p f ell (probe p f bits)) =
      J6ActiveInterpolation.scalarIn q f ell (probe q f bits) := by
  unfold lowerBox J6ActiveInterpolation.scalarIn
  rw [adjoinMap_of]
  congr 1
  exact same_probe_at_higher_precision q p hqp f bits

theorem lower_base_reduce (p q : ℕ) (hqp : q≤p) :
    (lowerBase p q hqp).comp (J6ZeroTransport.reduceBase p)=J6ZeroTransport.reduceBase q :=
  J6ZeroTransport.ringHom_unique _ _

theorem lower_scalar_reduce (p q : ℕ) (hqp : q≤p) (f : ℤ[X]) :
    (lowerScalar p q hqp f).comp (J6R9Recursive.reduceScalar p f)=J6R9Recursive.reduceScalar q f := by
  ext x
  obtain ⟨w,rfl⟩ := AdjoinRoot.mk_surjective x
  rw [RingHom.comp_apply,J6R9Recursive.reduceScalar,adjoinMap_mk,lowerScalar,NativeProbeRing.reduceScalar_mk,
    Polynomial.map_map]
  change AdjoinRoot.mk (liftPoly q f) (w.map ((lowerBase p q hqp).comp (J6ZeroTransport.reduceBase p))) = _
  rw [lower_base_reduce,J6R9Recursive.reduceScalar,adjoinMap_mk]

theorem lower_box_reduce (p q : ℕ) (hqp : q≤p) (f : ℤ[X]) (ell : ℕ) :
    (lowerBox p q hqp f ell).comp (reduce p f ell)=reduce q f ell := by
  ext x
  obtain ⟨w,rfl⟩ := AdjoinRoot.mk_surjective x
  rw [RingHom.comp_apply,reduce,adjoinMap_mk,lowerBox,adjoinMap_mk,
    Polynomial.map_map,lower_scalar_reduce,reduce,adjoinMap_mk]


section Projection
open P11FullPacking J6R10Repack J6R11Integral J6R9PacketScopes

variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

/-- Lower precision reduces every one of the very same frozen integer child
values. No mode is replaced, and no child is recompiled. -/
theorem lower_actual_product (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p q : ℕ) (hqp : q≤p) (z : Box f ell p)
    (file : EntryFile f ell N) (hf : f.Monic) (β : Mode i p P.mask →₀ ℕ) :
    lowerBox p q hqp f ell (J9R15FrozenErasurePhysical.actualProjection P i ht hv p z file hf β) =
      ∏ g : G, reduce q f ell (actualChildTruth P i ht hv p z file hf β g) := by
  rw [J9R15FrozenErasurePhysical.actualProjection,map_prod]
  apply Finset.prod_congr rfl
  intro g _
  exact RingHom.congr_fun (lower_box_reduce p q hqp f ell) _

#print axioms lower_actual_product
end Projection
#print axioms lower_binary_address
#print axioms lower_base_reduce
#print axioms lower_scalar_reduce
#print axioms lower_box_reduce
end
end J9R15FrozenErasurePrecision
