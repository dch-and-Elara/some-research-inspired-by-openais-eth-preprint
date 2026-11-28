import J6R19RetainedBox
import J6R9RecursiveReadout

/-! Coordinate compatibility for checking the entire scaled U/V
register. This uses additive monic coordinates and true residue
reduction; the section of least values is never used as a map of
rings. The actual bit traversal lives in ScheduleWeightStrip. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open Polynomial AOracleCoordinates J6R9Recursive NativeProbeRing

theorem coord_natSMul {q : ℕ} (f : (ZMod (2^q))[X]) (hf : f.Monic) (ell : ℕ)
    (ij : Fin f.natDegree×Fin ell) (x : Truncated f ell) (n : ℕ) :
    doubleCoord f hf ell ij ((n:Truncated f ell)*x)=
      (n:ZMod (2^q))*doubleCoord f hf ell ij x := by
  rw [←nsmul_eq_mul,←nsmul_eq_mul,map_nsmul]

theorem coord_scale_two {q : ℕ} (f : (ZMod (2^q))[X]) (hf : f.Monic) (ell : ℕ)
    (ij : Fin f.natDegree×Fin ell) (x : Truncated f ell) (B : ℕ) :
    doubleCoord f hf ell ij ((2:Truncated f ell)^B*x)=
      (2:ZMod (2^q))^B*doubleCoord f hf ell ij x := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using coord_natSMul f hf ell ij x (2^B)

noncomputable def lowerUV (p q : ℕ) (hle : p≤q) (f : ℤ[X]) (ell : ℕ) :
    Box f ell q→+*Box f ell p :=
  adjoinMap (NativeProbeRing.reduceScalar p q hle f) (X^ell) (X^ell) (by simp)

theorem lowerUV_coord (p q : ℕ) (hle : p≤q) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ)
    (sameDegree : (liftPoly q f).natDegree=(liftPoly p f).natDegree)
    (i : Fin (liftPoly q f).natDegree) (iv : Fin ell) (x : Box f ell q) :
    let j : Fin (liftPoly p f).natDegree := Fin.cast sameDegree i
    doubleCoord (liftPoly p f) (hf.map _) ell (j,iv) (lowerUV p q hle f ell x)=
      NativeProbeRing.reduceBase p q hle (doubleCoord (liftPoly q f) (hf.map _) ell (i,iv) x) := by
  let φ := NativeProbeRing.reduceScalar p q hle f
  let γ := NativeProbeRing.reduceBase p q hle
  unfold doubleCoord
  dsimp only [AddMonoidHom.comp_apply]
  rw [coord_apply,coord_apply,show (AdjoinRoot.modByMonicHom (monic_X.pow ell) (lowerUV p q hle f ell x))=
      (AdjoinRoot.modByMonicHom (monic_X.pow ell) x).map φ from adjoinMap_normal _ _ _ _ _ x,
    Polynomial.coeff_map]
  have inner (v : Scalar q f) :
      AdjoinRoot.modByMonicHom (hf.map _) (φ v)=
        (AdjoinRoot.modByMonicHom (hf.map _) v).map γ := by
    induction v using AdjoinRoot.induction_on with
    | _ z =>
      let pMon : (liftPoly p f).Monic := hf.map _
      let qMon : (liftPoly q f).Monic := hf.map _
      change AdjoinRoot.modByMonicHom pMon
          (φ (AdjoinRoot.mk (liftPoly q f) z))=
        (AdjoinRoot.modByMonicHom qMon (AdjoinRoot.mk (liftPoly q f) z)).map γ
      rw [show φ (AdjoinRoot.mk (liftPoly q f) z)=AdjoinRoot.mk (liftPoly p f) (z.map γ) from
        NativeProbeRing.reduceScalar_mk p q hle f z,AdjoinRoot.modByMonicHom_mk pMon,
        AdjoinRoot.modByMonicHom_mk qMon,Polynomial.map_modByMonic γ qMon,NativeProbeRing.reduce_liftPoly]
  unfold AOracleCoordinates.coord
  dsimp only [LinearMap.toAddMonoidHom_coe,LinearMap.comp_apply,Polynomial.lcoeff_apply, Fin.coe_cast]
  let v : Scalar q f := (AdjoinRoot.modByMonicHom (monic_X.pow ell) x).coeff iv.val
  change (AdjoinRoot.modByMonicHom (hf.map (Int.castRingHom (NativeProbeRing.Base p))) (φ v)).coeff i.val =
    γ ((AdjoinRoot.modByMonicHom (hf.map (Int.castRingHom (NativeProbeRing.Base q))) v).coeff i.val)
  rw [inner v,Polynomial.coeff_map]
 
theorem base_lower_is_natVal (p q : ℕ) (h : p≤q) (x : NativeProbeRing.Base q) :
    NativeProbeRing.reduceBase p q h x=(x.val:NativeProbeRing.Base p) := by
  haveI : NeZero (2^q:ℕ) := ⟨by positivity⟩
  conv_lhs => rw [←ZMod.natCast_zmod_val x,map_natCast]

#print axioms coord_scale_two
#print axioms lowerUV_coord
#print axioms base_lower_is_natVal
end J6R23ScheduleWeight



