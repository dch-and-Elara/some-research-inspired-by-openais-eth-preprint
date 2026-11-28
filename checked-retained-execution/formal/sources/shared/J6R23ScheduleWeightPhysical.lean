import J6R23ScheduleWeightCoordinates
import J6R23ScheduleWeightStrip
import J6R19RetainedWords

/-! Derive physical low-bit checks from a single exact scaled native
box equality. One must not assume divisibility of the decoded
coordinate words separately. The coefficients are those of the
actual descending tape, via the A1 paid scan. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open A1R10 A1R11 AOracleCoordinates AOracleMachineTime AOracleMachineTimeTape
open J6R19Retained J6R22Active

theorem scanWord_get {A : Type*} (G : Gates A) (xs : List A) (i : ℕ) (hi : i<xs.length) :
    (scanWord G i xs).result=xs[i] := by
  rw [(scanWord_exact G xs i).1,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  rfl

theorem uvScan_get {q ell : ℕ} (hq : 0<q) {fw : List (Word q)}
    (v : UVBlock fw ell) (i j : ℕ)
    (hj : j<v.val.length) (hi : i<v.val[j].val.length) :
    (uvScan hq v i j).result=v.val[j].val[i] := by
  change (scanWord (wordOps q hq).toGates i (scanWord (uGates hq fw) j v.val).result.val).result=_
  rw [scanWord_get (uGates hq fw) v.val j hj,scanWord_get _ _ i hi]

set_option maxHeartbeats 650000 in
theorem scaled_frame_raw_words {p B ell : ℕ} (hq : 0<p+B)
    {fw : List (Word (p+B))} (v : UVBlock fw ell)
    (x : Truncated (Modulus (p+B) hq fw) ell)
    (hs : uvRead hq fw ell v=(2:Truncated (Modulus (p+B) hq fw) ell)^B*x) :
    ∀ row∈v.val,∀ w∈row.val,2^B∣bitsValue w.val := by
  let q := p+B
  let F := Modulus q hq fw
  letI : Fact (1<(2:ℕ)^q) := ⟨one_lt_pow₀ (by decide) hq.ne'⟩
  obtain ⟨hD,hM⟩ := modulus_degree (wordOps q hq) fw
  have hm : F.Monic := hM
  have hD' : F.natDegree=fw.length := hD
  intro row hr w hw
  obtain ⟨j,hj,eJ⟩ := List.getElem_of_mem hr
  obtain ⟨i,hi,eI⟩ := List.getElem_of_mem hw
  have hi' : i < v.val[j].val.length := by rw [eJ]; exact hi
  let I : Fin fw.length := ⟨i,by rw [←row.property]; exact hi⟩
  let V : Fin ell := ⟨j,by rw [←v.property]; exact hj⟩
  let uv : Fin F.natDegree×Fin ell := (⟨fw.length-1-i,by have h:=I.isLt; omega⟩,⟨ell-1-j,by have h:=V.isLt; omega⟩)
  have get : (uvScan hq v i j).result=w := by
    have hGet := uvScan_get hq v i j hj hi'
    rw [hGet]
    have T (x y : UBlock fw) (h : x=y) (ix : i<x.val.length) (iy : i<y.val.length) :
        x.val[i]'ix=y.val[i]'iy := by subst y; rfl
    exact (T _ _ eJ hi' hi).trans eI
  have native := uvScan_native hq v I V hm hD'
  change wordRead (uvScan hq v i j).result=doubleCoord F hm ell uv (uvRead hq fw ell v) at native
  rw [get,hs,coord_scale_two] at native
  let value := doubleCoord F hm ell uv x
  have hw' : wordRead w=(2:NativeProbeRing.Base q)^B*value.val := by
    rw [native]
    exact congrArg (fun z : NativeProbeRing.Base q=>(2:NativeProbeRing.Base q)^B*z)
      (ZMod.natCast_zmod_val _).symm
  have d := high_word_requires_exact_divisibility p B value.val
  dsimp only at d
  rw [←hw',wordLeast] at d
  exact d.1

theorem scaled_frame_checked_strip {p B ell : ℕ} (hq : 0<p+B)
    {fw : List (Word (p+B))} {low : List (Word p)}
    (eq : fw.length=low.length) (v : UVBlock fw ell)
    (x : Truncated (Modulus (p+B) hq fw) ell)
    (hs : uvRead hq fw ell v=(2:Truncated (Modulus (p+B) hq fw) ell)^B*x) :
    ∃ u,(stripUVLoop eq v).result=some u ∧
      List.Forall₂ (fun a b=>List.Forall₂ (fun x y=>bitsValue y.val=bitsValue x.val/2^B) a.val b.val)
        v.val u.val ∧
      (stripUVLoop eq v).steps≤6+ell*(10+fw.length*(8*(p+B+1)+p+8)+low.length*p) :=
  stripUVLoop_correct eq v (scaled_frame_raw_words hq v x hs)

#print axioms uvScan_get
#print axioms scaled_frame_raw_words
#print axioms scaled_frame_checked_strip
end J6R23ScheduleWeight




