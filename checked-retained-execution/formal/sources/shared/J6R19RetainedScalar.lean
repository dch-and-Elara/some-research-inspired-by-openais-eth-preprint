import J6R19RetainedWords
import J6R19RetainedNormal

/-! Exact change of precision for one inner monic register. The
canonical section takes the least representatives at the ORIGINAL
modulus, not at the receiving modulus. -/
namespace J6R19Retained
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime AOracleCoordinates
open J6R9Recursive DenominatorBudget

theorem size_of_monic_words {p : ℕ} (hp : 0<p) {f : ℤ[X]} (hf : f.Monic)
    {ws : List (Word p)} (h : Modulus p hp ws=NativeProbeRing.liftPoly p f) :
    ws.length=f.natDegree := by
  letI : Fact (1<(2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  have hD := (modulus_degree (wordOps p hp) ws).1
  change (Modulus p hp ws).natDegree=ws.length at hD
  rw [h,show (NativeProbeRing.liftPoly p f).natDegree=f.natDegree from hf.natDegree_map _] at hD
  exact hD.symm

theorem scalarAfter_zero (p q : ℕ) {f : ℤ[X]} (hf : f.Monic) :
    reduceScalar q f (canonicalScalar p f hf 0)=0 := by
  simp [canonicalScalar,polynomialSection]

set_option maxHeartbeats 850000 in
theorem native_resizeU {p q : ℕ} (hp : 0<p) (hq : 0<q) {f : ℤ[X]} (hf : f.Monic)
    {old : List (Word p)} {new : List (Word q)}
    (hO : Modulus p hp old=NativeProbeRing.liftPoly p f)
    (hN : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (he : old.length=new.length) (v : UBlock old) :
    transportU hN (uRead hq new (resizeU he v).result)=
      reduceScalar q f (canonicalScalar p f hf (transportU hO (uRead hp old v))) := by
  letI : Fact (1<(2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  let o := wordOps p hp
  let n := wordOps q hq
  let M : (NativeProbeRing.liftPoly p f).Monic := hf.map _
  have hW : v.val.length ≤ (NativeProbeRing.liftPoly p f).natDegree := by
    rw [v.property,size_of_monic_words hp hf hO,show (NativeProbeRing.liftPoly p f).natDegree=f.natDegree from hf.natDegree_map _]
  have hNF := normal_mapped o (RingHom.id _) M v.val hW
  rw [Polynomial.map_id] at hNF
  have hZ : (J6ZeroTransport.reduceBase q ∘ finiteCoeffLift p) 0=0 := by simp [finiteCoeffLift]
  have hEq (w : Word p) :
      (J6ZeroTransport.reduceBase q ∘ finiteCoeffLift p) ((RingHom.id _) (o.read w)) =
        (RingHom.id _) (n.read (resizeWord q w).result) := by
    change J6ZeroTransport.reduceBase q (finiteCoeffLift p (wordRead w)) =
      wordRead (resizeWord q w).result
    rw [(resizeWord_exact q w).1,finiteCoeffLift,map_natCast]
  have hD := section_decode_map o n (RingHom.id _) (RingHom.id _)
    (J6ZeroTransport.reduceBase q ∘ finiteCoeffLift p) hZ (fun w=>(resizeWord q w).result) hEq v.val
  rw [Polynomial.map_id,Polynomial.map_id] at hD
  unfold uRead
  rw [transportU_mk,transportU_mk]
  change AdjoinRoot.mk (NativeProbeRing.liftPoly q f) (decode n (resizeU he v).result.val) =
    reduceScalar q f (AdjoinRoot.mk (intPoly f) (polynomialSection (finiteCoeffLift p)
      (AdjoinRoot.modByMonicHom M (AdjoinRoot.mk (NativeProbeRing.liftPoly p f) (decode o v.val)))))
  rw [hNF,reduceScalar,adjoinMap_mk,section_push,hD,(resizeU_exact he v).1]

#print axioms size_of_monic_words
#print axioms scalarAfter_zero
#print axioms native_resizeU
end J6R19Retained



