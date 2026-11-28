import J6R23ScheduleWeightCompile
import J6R22ActiveCoeff
import J6R19RetainedBox
import J6R9RecursiveAssemble

/-! A full weighted Taylor *term* from an actual jet tape. Scan its
jth coefficient, canonically resize the original p_t-bit U/V word,
generate the scaled source weight at the receiving width, then
multiply with native bit kernels. Computing the jet itself and
where to install its tape are not charged as zero. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open Polynomial A1R10 A1R12 AOracleCoordinates AOracleMachineTime
open P1DyadicGrid HermiteLoss J6ActiveSchedule J6R22Active J6R9Recursive
open J6R19Retained

variable {p q ell k : ℕ} {old : List (Word p)} {new : List (Word q)}

def termM (hp : 0<p) (hOld : 0<old.length) (hq : 0<q) (hNew : 0<new.length)
    (hv : 0<ell) (hWidth : old.length=new.length)
    (jet : JetTape old ell k) (a B j : ℕ) (t : ℤ) (xs : List (ℤ×ℕ)) :
    Meter (UVBlock new ell) :=
  let x := jetCoeffM hp hOld jet j
  let y := resizeUV hWidth x.result
  let w := rawWeight hq hNew hv a B j t xs
  mulM hq w ⟨y.result,x.steps+y.steps+4⟩

def termFee (e ell p q a B k j : ℕ) (hq : 0<q) (t : ℤ) (xs : List (ℤ×ℕ)) : ℕ :=
  jetCoeffFee e ell p k+boxFee e ell p q+rawWeightFee e ell q a B j hq t xs+
    mulCap e ell q+6

set_option maxHeartbeats 900000 in
theorem termM_exact (hp : 0<p) (hOld : 0<old.length) (hq : 0<q) (hNew : 0<new.length)
    (hv : 0<ell) {f : ℤ[X]} (hf : f.Monic)
    (hO : Modulus p hp old=NativeProbeRing.liftPoly p f)
    (hN : Modulus q hq new=NativeProbeRing.liftPoly q f)
    {a M u B j : ℕ} {t : ℤ} (ht : t∈active a M u) (hB : totalLoss a (sourceH M u) j t≤B)
    (L : Roster a M u t) (jet : JetTape old ell k) (hj : j<k) (F : (Box f ell p)[X])
    (recv : jetMap (boxTransport hO) k (jetRead hp hOld jet)=AdjoinRoot.mk (X^k) F) :
    let hs := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
    let T := termM hp hOld hq hNew hv hs jet a B j t L.rows
    boxTransport hN (uvRead hq new ell T.result)=
      reduce q f ell (localScalar f ell (scaledWeight a u (sourceH M u) B j t)*
        representative p f ell (F.coeff j)) ∧
    T.steps≤termFee f.natDegree ell p q a B k j hq t L.rows := by
  let H := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
  let x := jetCoeffM hp hOld jet j
  let y := resizeUV H x.result
  let w := rawWeight hq hNew hv a B j t L.rows
  have he : 0<f.natDegree := size_of_monic_words hp hf hO ▸ hOld
  have ⟨hx,hxC⟩ := jetCoeffM_exact hp hOld (boxTransport hO) jet j hj F recv
  have ⟨hy,hyC⟩ := native_resizeUV hp hq hf he hO hN x.result
  have ⟨hw,hwC⟩ := rawWeight_exact hq hNew hv ht hB L
  have hW : (boxTransport (ell:=ell) hN).comp (localReduce hq new ell)=
      (reduce q f ell).comp (localScalar f ell) :=
    J6ZeroTransport.ringHom_unique _ _
  constructor
  · change boxTransport hN (uvRead hq new ell (mulM hq w ⟨y.result,x.steps+y.steps+4⟩).result)=_
    have hw' : boxTransport hN (uvRead hq new ell w.result)=
        reduce q f ell (localScalar f ell (scaledWeight a u (sourceH M u) B j t)) := by
      rw [hw]
      exact DFunLike.congr_fun hW _
    have hy' : boxTransport hN (uvRead hq new ell y.result)=
        reduce q f ell (representative p f ell (F.coeff j)) := by
      rw [boxTransport_cast,hy,←boxTransport_cast,hx,representative,dif_pos hf]
    rw [mulM_read,map_mul,hw',show uvRead hq new ell (Meter.mk y.result (x.steps+y.steps+4)).result=
      uvRead hq new ell y.result from rfl,hy',map_mul]
  · have hx' : x.steps≤jetCoeffFee f.natDegree ell p k := by
      simpa only [size_of_monic_words hp hf hO] using hxC
    have hy' : y.steps≤boxFee f.natDegree ell p q := hyC
    have hw' : w.steps≤rawWeightFee f.natDegree ell q a B j hq t L.rows := by
      simpa only [size_of_monic_words hq hf hN] using hwC
    have hm := mulM_cost hq w (Meter.mk y.result (x.steps+y.steps+4))
    change (mulM hq w (Meter.mk y.result (x.steps+y.steps+4))).steps ≤
      w.steps+(x.steps+y.steps+4)+mulCap new.length ell q+2 at hm
    rw [size_of_monic_words hq hf hN] at hm
    change (mulM hq w (Meter.mk y.result (x.steps+y.steps+4))).steps ≤ _
    unfold termFee
    omega

#print axioms termM_exact
end J6R23ScheduleWeight


