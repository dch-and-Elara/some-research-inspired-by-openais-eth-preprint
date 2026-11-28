import J6R23ScheduleWeightRestore
import J6R23ScheduleWeightAssemble

/-! Exact receiving tower and checked finishing program. This is an
equivalent finite arithmetic implementation, not a complexity
charge for the textual rational-fraction evaluation. Building
the recursion's stored descriptors/jet frames is not free. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime
open J6R22Active J6R9Recursive J6R19Retained

theorem lowerScalar_reduction (p q : ℕ) (h : p≤q) (f : ℤ[X]) (z : IntScalar f) :
    NativeProbeRing.reduceScalar p q h f (reduceScalar q f z)=reduceScalar p f z := by
  induction z using AdjoinRoot.induction_on with
  | _ P =>
    let low := NativeProbeRing.reduceBase p q h
    have hbase : low.comp (J6ZeroTransport.reduceBase q)=J6ZeroTransport.reduceBase p :=
      J6ZeroTransport.ringHom_unique _ _
    change NativeProbeRing.reduceScalar p q h f
      (adjoinMap _ _ _ _ (AdjoinRoot.mk (intPoly f) P))=adjoinMap _ _ _ _ (AdjoinRoot.mk (intPoly f) P)
    rw [adjoinMap_mk,NativeProbeRing.reduceScalar_mk,adjoinMap_mk,Polynomial.map_map,hbase]

theorem lowerUV_reduction (p q : ℕ) (h : p≤q) (f : ℤ[X]) (ell : ℕ) (z : IntRing f ell) :
    lowerUV p q h f ell (reduce q f ell z)=reduce p f ell z := by
  induction z using AdjoinRoot.induction_on with
  | _ P =>
    have hs : (NativeProbeRing.reduceScalar p q h f).comp (reduceScalar q f)=reduceScalar p f :=
      RingHom.ext (lowerScalar_reduction p q h f)
    unfold lowerUV J6R9Recursive.reduce
    rw [adjoinMap_mk,adjoinMap_mk,adjoinMap_mk,Polynomial.map_map,hs]

def activeFinishM {p B ell : ℕ} {high : List (Word (p+B))} {low : List (Word p)}
    (hq : 0<p+B) (he : high.length=low.length)
    (centres : List (ℤ×ℕ)) (terms : ℤ→ℕ→Meter (UVBlock high ell)) :
    Meter (Option (UVBlock low ell)) :=
  let a := allTerms hq terms centres
  let b := stripUVLoop he a.result
  ⟨b.result,a.steps+b.steps+4⟩

set_option maxHeartbeats 1000000 in
theorem activeFinish_value {p B ell : ℕ} {high : List (Word (p+B))} {low : List (Word p)}
    (hp : 0<p) (hq : 0<p+B) (hv : 0<ell) {f : ℤ[X]} (hf : f.Monic) (he : 0<f.natDegree)
    (hH : Modulus (p+B) hq high=NativeProbeRing.liftPoly (p+B) f)
    (hL : Modulus p hp low=NativeProbeRing.liftPoly p f)
    (centres : List (ℤ×ℕ)) (terms : ℤ→ℕ→Meter (UVBlock high ell))
    (out : IntRing f ell)
    (hResult : boxTransport hH (uvRead hq high ell (allTerms hq terms centres).result)=
      (2:Box f ell (p+B))^B*reduce (p+B) f ell out) :
    let h := (size_of_monic_words hq hf hH).trans (size_of_monic_words hp hf hL).symm
    let op := activeFinishM hq h centres terms
    ∃ u, op.result=some u ∧ boxTransport hL (uvRead hp low ell u)=reduce p f ell out ∧
      op.steps≤termBill terms centres+termsLoopFee high.length ell (p+B) hq centres+
        (6+ell*(10+high.length*(8*(p+B+1)+p+8)+low.length*p))+4 := by
  let a := allTerms hq terms centres
  let h := (size_of_monic_words hq hf hH).trans (size_of_monic_words hp hf hL).symm
  let b := stripUVLoop h a.result
  obtain ⟨u,hs,hw,hc⟩ := restore_native_box hp hq hf he hv hH hL a.result _ hResult
  refine ⟨u,hs,hw.trans (lowerUV_reduction p (p+B) (by omega) f ell out),?_⟩
  change a.steps+b.steps+4≤_
  have hA : a.steps≤termBill terms centres+termsLoopFee high.length ell (p+B) hq centres :=
    allTerms_steps hq terms centres
  have hC : b.steps≤6+ell*(10+high.length*(8*(p+B+1)+p+8)+low.length*p) := hc
  omega

#print axioms lowerScalar_reduction
#print axioms lowerUV_reduction
#print axioms activeFinish_value
end J6R23ScheduleWeight


