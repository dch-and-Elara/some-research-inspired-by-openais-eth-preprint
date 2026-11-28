import J6R23ScheduleWeightCoordScan
import J6R22ActiveCenter

/-! Read the complete paid checked shift as the actual low-precision
monic box. The tall frame is known to be the exact shifted image,
not merely close coordinatewise. All word checks are certified from
that equality, and the low frame denotes true residue projection. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open Polynomial A1R10 AOracleCoordinates AOracleMachineTime AOracleMachineTimeTape
open J6R22Active J6R19Retained J6R9Recursive

set_option maxHeartbeats 1400000 in
theorem restore_native_box {p B ell : ℕ} (hp : 0<p) (hq : 0<p+B)
    {old : List (Word (p+B))} {new : List (Word p)}
    {f : ℤ[X]} (hf : f.Monic) (he : 0<f.natDegree) (hv : 0<ell)
    (hO : Modulus (p+B) hq old=NativeProbeRing.liftPoly (p+B) f)
    (hN : Modulus p hp new=NativeProbeRing.liftPoly p f)
    (v : UVBlock old ell) (x : Box f ell (p+B))
    (scaled : boxTransport hO (uvRead hq old ell v)=(2:Box f ell (p+B))^B*x) :
    let h := (size_of_monic_words hq hf hO).trans (size_of_monic_words hp hf hN).symm
    let z := stripUVLoop h v
    ∃ u,z.result=some u ∧ boxTransport hN (uvRead hp new ell u)=lowerUV p (p+B) (by omega) f ell x ∧
      z.steps≤6+ell*(10+old.length*(8*(p+B+1)+p+8)+new.length*p) := by
  let q := p+B
  letI : Fact (1<(2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  letI : Fact (1<(2:ℕ)^q) := ⟨one_lt_pow₀ (by decide) hq.ne'⟩
  have eO := size_of_monic_words hq hf hO
  have eN := size_of_monic_words hp hf hN
  have hs : old.length=new.length := eO.trans eN.symm
  have hEq : uvRead hq old ell v=(2:Truncated (Modulus q hq old) ell)^B*pullRing hO x := by
    apply boxTransport_injective hO
    rw [scaled,map_mul,map_pow,map_ofNat,transport_pull]
  obtain ⟨u,hval,rel,cost⟩ := scaled_frame_checked_strip hq hs v (pullRing hO x) hEq
  refine ⟨u,hval,?_,cost⟩
  let FO := NativeProbeRing.liftPoly q f
  let FN := NativeProbeRing.liftPoly p f
  let hn : FN.Monic := hf.map _
  let ho : FO.Monic := hf.map _
  have fdO : FO.natDegree=f.natDegree := hf.natDegree_map _
  have fdN : FN.natDegree=f.natDegree := hf.natDegree_map _
  have hnD : 0<FN.natDegree := fdN.symm ▸ he
  have hD : FO.natDegree=FN.natDegree := fdO.trans fdN.symm
  let le : p≤q := by omega
  apply doubleCoord_injective hp FN hn hnD ell hv
  funext ij
  let i := ij.1
  let j := ij.2
  let iO : Fin FO.natDegree := Fin.cast hD.symm i
  let a := new.length-1-i.val
  let aa := old.length-1-iO.val
  let b := ell-1-j.val
  have ha : a=aa := by dsimp [a,aa,iO]; rw [hs]
  have ib : i.val<new.length := (fdN.trans eN.symm) ▸ i.isLt
  have ia : a<new.length := by unfold a; omega
  have bb : b<ell := by unfold b; have := j.isLt; omega
  have hb1 : b<v.val.length := v.property.symm ▸ bb
  have hb2 : b<u.val.length := u.property.symm ▸ bb
  let rO := v.val[b]
  let rN := u.val[b]
  have ia1 : a<rO.val.length := by rw [rO.property,hs]; exact ia
  have ia2 : a<rN.val.length := rN.property.symm ▸ ia
  have hR := rel.get hb1 hb2
  change List.Forall₂ (fun x y=>bitsValue y.val=bitsValue x.val/2^B) rO.val rN.val at hR
  have words := hR.get ia1 ia2
  let oldW := (uvScan hq v a b).result
  let newW := (uvScan hp u a b).result
  have H : bitsValue newW.val=bitsValue oldW.val/2^B := by
    simp only [oldW,newW,uvScan_get hq v a b hb1 ia1,uvScan_get hp u a b hb2 ia2]
    exact words
  have newRead := native_uvScan_coeff hp hf hN u i j
  change wordRead newW=doubleCoord FN hn ell (i,j) (boxTransport hN (uvRead hp new ell u)) at newRead
  have oldRead := native_uvScan_coeff hq hf hO v iO j
  change wordRead (uvScan hq v aa b).result=doubleCoord FO ho ell (iO,j) (boxTransport hO (uvRead hq old ell v)) at oldRead
  rw [←ha,scaled,coord_scale_two] at oldRead
  let c0 := doubleCoord FO ho ell (iO,j) x
  have vv : wordRead oldW=(2:NativeProbeRing.Base q)^B*c0.val :=
    oldRead.trans (congrArg (fun y : NativeProbeRing.Base q=>(2:NativeProbeRing.Base q)^B*y)
      (ZMod.natCast_zmod_val _).symm)
  have hoD := (high_word_requires_exact_divisibility p B c0.val).2
  rw [←vv,wordLeast] at hoD
  have hWord : wordRead newW=(c0.val:NativeProbeRing.Base p) := by
    change (bitsValue newW.val:NativeProbeRing.Base p)=_
    rw [H,hoD,ZMod.natCast_mod]
  have lower := lowerUV_coord p q le f hf ell hD iO j x
  have rev : Fin.cast hD iO=i := Fin.ext rfl
  dsimp only at lower
  rw [rev] at lower
  change doubleCoord FN hn ell (i,j) (boxTransport hN (uvRead hp new ell u))=
    doubleCoord FN hn ell (i,j) (lowerUV p q le f ell x)
  exact newRead.symm.trans (hWord.trans ((base_lower_is_natVal p q le c0).symm.trans lower.symm))

#print axioms restore_native_box
end J6R23ScheduleWeight




