import J6R23ScheduleWeightPhysical
import J6R22ActiveUnit

/-! For the physical coefficient scan, transport the raw monic
polynomial to the printed f at the same native precision. The two
descending offsets are explicitly reversed; neither a field nor an
arbitrary layout inverse is used for these reads. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open Polynomial A1R10 AOracleCoordinates AOracleMachineTime
open J6R22Active J6R19Retained J6R9Recursive

theorem coord_boxTransport {p ell : ℕ} {P Q : (ZMod (2^p))[X]} (eq : P=Q)
    (hp : P.Monic) (hq : Q.Monic)
    (i : Fin P.natDegree) (j : Fin ell) (x : Truncated P ell) :
    doubleCoord Q hq ell (Fin.cast (congrArg natDegree eq) i,j) (boxTransport eq x)=
      doubleCoord P hp ell (i,j) x := by
  subst Q
  rfl

set_option maxHeartbeats 800000 in
theorem native_uvScan_coeff {p ell : ℕ} (hp : 0<p) {fw : List (Word p)}
    {f : ℤ[X]} (hf : f.Monic)
    (hF : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (v : UVBlock fw ell)
    (i : Fin (NativeProbeRing.liftPoly p f).natDegree) (j : Fin ell) :
    wordRead (uvScan hp v (fw.length-1-i.val) (ell-1-j.val)).result=
      doubleCoord (NativeProbeRing.liftPoly p f) (hf.map _) ell (i,j)
        (boxTransport hF (uvRead hp fw ell v)) := by
  letI : Fact (1<(2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  let F := Modulus p hp fw
  have ⟨hd,hm⟩ := modulus_degree (wordOps p hp) fw
  change F.natDegree=fw.length at hd
  have hmF : F.Monic := hm
  have hob : (NativeProbeRing.liftPoly p f).natDegree=fw.length := by rw [←hF]; exact hd
  have hi : i.val<fw.length := hob ▸ i.isLt
  let iR : Fin fw.length := ⟨fw.length-1-i.val,by omega⟩
  let jR : Fin ell := ⟨ell-1-j.val,by have := j.isLt; omega⟩
  have hRead := uvScan_native hp v iR jR hmF hd
  have fi : fw.length-1-iR.val=i.val := by
    change fw.length-1-(fw.length-1-i.val)=i.val
    omega
  have fj : ell-1-jR.val=j.val := by
    change ell-1-(ell-1-j.val)=j.val
    have := j.isLt
    omega
  let i0 : Fin F.natDegree := ⟨fw.length-1-iR.val,by rw [hd,fi];exact hi⟩
  let j0 : Fin ell := ⟨ell-1-jR.val,by rw [fj];exact j.isLt⟩
  have hT := coord_boxTransport hF hmF (hf.map _) i0 j0 (uvRead hp fw ell v)
  have hi0 : Fin.cast (congrArg natDegree hF) i0=i := Fin.ext fi
  have hj0 : j0=j := Fin.ext fj
  have ht : doubleCoord (NativeProbeRing.liftPoly p f) (hf.map _) ell (i,j)
      (boxTransport hF (uvRead hp fw ell v))=doubleCoord F hmF ell (i0,j0) (uvRead hp fw ell v) := by
    simpa only [hi0,hj0] using hT
  exact hRead.trans ht.symm

#print axioms coord_boxTransport
#print axioms native_uvScan_coeff
end J6R23ScheduleWeight


