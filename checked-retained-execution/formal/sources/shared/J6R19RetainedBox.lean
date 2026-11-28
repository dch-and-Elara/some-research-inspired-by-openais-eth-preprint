import J6R19RetainedScalar

/-! The fitted physical U/V box, after word resizing, is exactly the
source's canonical lifting choice reduced to the current precision.
The least-residue section is not used as an algebra homomorphism. -/
namespace J6R19Retained
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime AOracleCoordinates
open J6R9Recursive J6R18ChildWrite J6R10Repack

theorem nativeScalar_nontrivial {p : ℕ} (hp : 0<p) {f : ℤ[X]} (hf : f.Monic)
    (he : 0<f.natDegree) : Nontrivial (NativeProbeRing.Scalar p f) := by
  letI : Fact (1<(2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  have hMon : (NativeProbeRing.liftPoly p f).Monic := hf.map _
  have hDegree : (NativeProbeRing.liftPoly p f).natDegree=f.natDegree := hf.natDegree_map _
  refine nontrivial_of_ne (1 : NativeProbeRing.Scalar p f) 0 ?_
  have H := AdjoinRoot.mk_ne_zero_of_natDegree_lt hMon
    (show (1 : (NativeProbeRing.Base p)[X])≠0 from one_ne_zero)
    (show (1 : (NativeProbeRing.Base p)[X]).natDegree<(NativeProbeRing.liftPoly p f).natDegree by
      rwa [natDegree_one,hDegree])
  simpa only [map_one] using H

set_option maxHeartbeats 1000000 in
theorem native_resizeUV {p q ell : ℕ} (hp : 0<p) (hq : 0<q) {f : ℤ[X]} (hf : f.Monic)
    (he : 0<f.natDegree) {old : List (Word p)} {new : List (Word q)}
    (hO : Modulus p hp old=NativeProbeRing.liftPoly p f)
    (hN : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (v : UVBlock old ell) :
    let hE := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
    let u := resizeUV hE v
    castBox hN (uvRead hq new ell u.result)=
      J6R9Recursive.reduce q f ell (canonicalLift p f hf ell (castBox hO (uvRead hp old ell v))) ∧
      u.steps≤boxFee f.natDegree ell p q := by
  let hE := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
  letI : Nontrivial (NativeProbeRing.Scalar p f) := nativeScalar_nontrivial hp hf he
  let T : (NativeProbeRing.Scalar p f)[X] := X^ell
  have H : v.val.length≤T.natDegree := by simp [T,v.property]
  have hNF := normal_mapped (uOps hp old) (transportU hO).toRingHom
    (monic_X.pow ell) v.val H
  have heD := section_decode_map (uOps hp old) (uOps hq new)
    (transportU hO).toRingHom (transportU hN).toRingHom
    (reduceScalar q f ∘ canonicalScalar p f hf) (scalarAfter_zero p q hf)
    (fun z=>(resizeU hE z).result) (fun z=>(native_resizeU hp hq hf hO hN hE z).symm) v.val
  obtain ⟨hD,hC⟩ := resizeUV_exact hE v
  refine ⟨?_,by simpa only [size_of_monic_words hp hf hO] using hC⟩
  change castBox hN (uvRead hq new ell (resizeUV hE v).result)=_
  simp only [uvRead,castBox_mk]
  rw [canonicalLift,hNF,J6R9Recursive.reduce,adjoinMap_mk,section_push,heD,hD]

theorem native_resize_read {X : Type*} {q ell : ℕ} {f : ℤ[X]} (hf : f.Monic)
    (he : 0<f.natDegree) (hq : 0<q) (d : CreatedEntry f ell X) (hp : 0<d.created)
    {old : List (Word d.created)} {new : List (Word q)}
    (hO : Modulus d.created hp old=NativeProbeRing.liftPoly d.created f)
    (hN : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (x : X) (v : UVBlock old ell)
    (hEntry : castBox hO (uvRead hp old ell v)=d.table x) :
    let hE := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
    let z := resizeUV hE v
    castBox hN (uvRead hq new ell z.result)=d.read hf q x ∧
      z.steps≤boxFee f.natDegree ell d.created q := by
  have H := native_resizeUV hp hq hf he hO hN v
  rw [hEntry] at H
  exact H

#print axioms nativeScalar_nontrivial
#print axioms native_resizeUV
#print axioms native_resize_read
end J6R19Retained


