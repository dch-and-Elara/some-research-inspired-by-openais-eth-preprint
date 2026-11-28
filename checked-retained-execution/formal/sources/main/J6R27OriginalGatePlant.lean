
import J6R27OriginalGateRun

/-! The producer really compiles the old source Plant incidence, including
literal signs, negative padding pins, free padding pins, and the two
actual subdivision-equality ports. It emits exactly the gate consumed
at descendant precision. The resident input is the original incidence
keys plus the current physical edge-address tape, not a gate truth table. -/
namespace J6R27OriginalGate
open scoped Polynomial
open AOracleMachineTime J6R10Repack J6R21Ancestor J6R21Leaf J6OrientedHost
open J6R11Blueprint J6R18ChildWrite
open A1R10 A1R11 A1R12

def produceGateWord {p ell b : ℕ} (hp : 0<p)
    {fw : List (A1R10.Word p)} (he : 0<fw.length) (hℓ : 0<ell)
    (built : Meter (Option (CodeGate (J6R15ModeCost.Word b)))) (bits : List Bool) :
    Meter (Option (UVBlock fw ell)) :=
  match built.result with
  | none => ⟨none,built.steps+3⟩
  | some A =>
    let r := runCode bits A
    ⟨some (if r.result then uvOne hp he hℓ else uvZero hp fw ell),
      built.steps+r.steps+uvWidth fw.length ell p+7⟩

theorem produced_gate_word {p ell n b : ℕ} (hp : 0<p)
    {fw : List (A1R10.Word p)} (he : 0<fw.length) (hℓ : 0<ell)
    (built : Meter (Option (CodeGate (J6R15ModeCost.Word b)))) (bits : List Bool)
    (A : OriginalGateTape n b) (h : built.result=some (forgetGate A)) :
    let b := uvGate hp he hℓ A bits
    (produceGateWord hp he hℓ built bits).result=some b.result ∧
    (produceGateWord hp he hℓ built bits).steps=built.steps+b.steps+3 := by
  unfold produceGateWord
  simp only [h,coded_run_is_original,uvGate,true_and]
  omega

variable {S V : Type} [LinearOrder S] [Fintype S] [Fintype V]
variable {f : ℤ[X]} {ell created m l q width : ℕ}

def sourcePlantGate (T : Plant V m q) (labels : Fin (J6Mesh.a m)→S)
    (v : PlantNode (b:=J6Mesh.K m) (l:=l) T labels)
    (code : J6OrientedHost.Wire labels m (J6Mesh.K m) l→J6R15ModeCost.Word width) :
    CodeGate (OriginSeed width) :=
  let Q := originalPortGate T labels v
  encodeGate (fun i=>⟨side (Q.port i).val,code (edge (Q.port i).val)⟩) Q.gate

set_option maxHeartbeats 2800000 in
theorem actual_original_emit_consume {current M b : ℕ}
    (T : Plant V m q) (labels : Fin (J6Mesh.a m)→S) (hf : f.Monic)
    (hp : 0<created) (hq : 0<current) (hF : 0<f.natDegree) (hℓ : 0<ell)
    {fw : List (A1R10.Word current)} (he : 0<fw.length)
    (hPoly : Modulus current hq fw=NativeProbeRing.liftPoly current f)
    (v : PlantNode (b:=J6Mesh.K m) (l:=l) T labels)
    (code : (actualOriginalPoint (f:=f) (ell:=ell) (created:=created) T labels v).host.Edge→
      J6R15ModeCost.Word width) (unique : Function.Injective code)
    {cur : Point f ell} (tr : Trace (actualOriginalPoint (created:=created) T labels v) cur)
    (ord : Fin M≃cur.host.Edge) (fit : M≤2^b) (hb : 0<b)
    (marks : List Bool) (hd : marks.length=tr.depth)
    (rows : List (J6R15ModeCost.Word (width+marks.length)))
    (trueRows : rows=List.ofFn (indexedKeys code tr ord marks hd))
    (x : Fin M→Bool) :
    let built := compileGate b marks rows (sourcePlantGate T labels v code)
    let op := produceGateWord hq he hℓ built (List.ofFn x)
    ∃ out, op.result=some out ∧
      castBox hPoly (uvRead hq fw ell out)=(entry cur).read hf current
        (assignment cur.host.network (x∘ord.symm) cur.vertex) ∧
      (entry cur).created=created ∧
      op.steps≤gateBuildCap width b marks.length M (originalPortGate T labels v).degree+
        originalGateFee M b (originalPortGate T labels v).degree+uvWidth fw.length ell current+7 := by
  let Q := originalPortGate T labels v
  let A := gateTape fit (tracedSlot tr ord ∘ Q.port) Q.gate
  let built := compileGate b marks rows (sourcePlantGate T labels v code)
  let out := uvGate hq he hℓ A (List.ofFn x)
  have E := compile_gate_exact hb code unique tr ord marks hd fit Q.port Q.gate rows trueRows
  have hv : built.result=some (forgetGate A) := by
    change (compileGate b marks rows (encodeGate (seedFrom code ∘ Q.port) Q.gate)).result=_
    rw [E.1]
    congr 1
    exact exact_code_is_forgotten fit (tracedSlot tr ord∘Q.port) Q.gate
  have hB : built.steps≤gateBuildCap width b marks.length M Q.degree := E.2
  have H := produced_gate_word hq he hℓ built (List.ofFn x) A hv
  obtain ⟨value,tag,paid⟩ := original_through_trace T labels hf hp hq hF hℓ he hPoly v tr
    ord fit A rfl x
  refine ⟨out.result,H.1,value,tag,?_⟩
  change (produceGateWord hq he hℓ built (List.ofFn x)).steps≤_
  rw [H.2]
  change out.steps≤originalGateFee M b Q.degree+uvWidth fw.length ell current+4 at paid
  change built.steps+out.steps+3≤gateBuildCap width b marks.length M Q.degree+
    originalGateFee M b Q.degree+uvWidth fw.length ell current+7
  omega

#print axioms produced_gate_word
#print axioms actual_original_emit_consume
end J6R27OriginalGate



