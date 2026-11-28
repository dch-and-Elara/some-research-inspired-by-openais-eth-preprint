import J6R64ActiveMachine
import J6R66BootPeakInit
import J6R66BootPeakShared

/-! Inspect the actual header and copy operands of the R66 replacement
preparer. At the real R62 per-centre handoff, the generated raw
record/weight arrays are measured before raw keys are no longer
needed. The returned coordinate weights are the same list, not a
second list charged from an equal decoded value. -/
namespace J6R68.RecursivePeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape
open J6R63Active J6R62ActivePrep J6R52FreshExterior J6R64Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R49DFS J6R32StatefulArithmetic
open J6R14LayoutCost J6R12CollisionEdges P11FullPacking J6R66.BootPeak
open J6R16ModeCost J6R21Ancestor
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3930
set_option maxHeartbeats 13500000
set_option Elab.async false

theorem real_mode_record_has_fixed_selected_width {a p tiles copies q : ℕ} {i : Fin a}
    (mode : PacketMode i copies tiles p) :
    (modeRowBits (encodeMode (q:=q) i mode)).length=6*a+6*a+q+q+q := by
  unfold modeRowBits encodeMode
  simp only [wordCell,coordinateLabel_len,List.length_append,Word.size]

private theorem width_mapped {A B : Type*} (encode : B→List Bool) (f : A→B)
    (xs : List A) (w : ℕ) (h : ∀ x,(encode (f x)).length=w) :
    bitSize encode (xs.map f)=xs.length*w := by
  change ((xs.map f).flatMap encode).length=_
  rw [List.flatMap_map]
  exact bitSize_exact (encode∘f) xs w h

noncomputable section
variable {f : ℤ[X]} {ell s q pw ew cw : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}
local notation "AA" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) c.depth)

def actualNativeRawCentre (hq : 0<q) (inp : CentreWords sel d t q) : Meter (RawTape q) :=
  canonicalRaw hq AA (centerIndex d t).val inp.copies inp.precision

def retainedHeaderControlBits (W : Meter (CallWords c pw ew)) (L : Meter (AtLayout sel d cw))
    (q : ℕ) : ℕ :=
  W.result.precision.bits.length+W.result.edges.bits.length+(copyOfLayout q L.result).result.bits.length

def currentCentreProducerBits (hq : 0<q) (inp : CentreWords sel d t q)
    (L : Meter (AtLayout sel d cw)) : ℕ :=
  let made := actualNativeRawCentre hq inp
  L.result.copies.bits.length+inp.precision.bits.length+
    bitSize modeRowBits made.result.modes+bitSize Word.bits made.result.weights+
    made.result.precision.bits.length

theorem actual_shared_control_bits_fit_the_fixed_registers
    (W : Meter (CallWords c pw ew)) (L : Meter (AtLayout sel d cw)) :
    retainedHeaderControlBits W L q=pw+ew+q := by
  unfold retainedHeaderControlBits
  rw [W.result.precision.size,W.result.edges.size,(copyOfLayout q L.result).result.size]

theorem exact_current_native_outputs_from_same_r66_active_tape
    (hq : 0<q) (ha : (centerIndex d t).val+1<q)
    (inp : CentreWords sel d t q) (L : Meter (AtLayout sel d cw)) :
    let tape := (fromWords hq ha inp).result
    let raw := actualNativeRawCentre hq inp
    tape.words=raw.result.weights ∧ tape.precision=raw.result.precision ∧
    tape.modes.map (encodeMode (centerIndex d t))=raw.result.modes ∧
    currentCentreProducerBits hq inp L=
      cw+q+tape.modes.length*(6*AA+6*AA+q+q+q)+tape.modes.length*q+q := by
  let raw := actualNativeRawCentre hq inp
  let tape := (fromWords hq ha inp).result
  have out := supplied_words_build_the_literal_tape hq ha inp
  have w : tape.words=raw.result.weights := out.1
  have p : tape.precision=raw.result.precision := out.2.1
  have m : tape.modes.map (encodeMode (centerIndex d t))=raw.result.modes := out.2.2.1
  have len : tape.words.length=tape.modes.length := by
    have val := congrArg List.length tape.weightMeaning
    simpa only [List.length_map] using val
  have payload :
      bitSize modeRowBits raw.result.modes=tape.modes.length*(6*AA+6*AA+q+q+q) := by
    rw [←m]
    exact width_mapped modeRowBits _ tape.modes _ real_mode_record_has_fixed_selected_width
  refine ⟨w,p,m,?_⟩
  change L.result.copies.bits.length+inp.precision.bits.length+
    bitSize modeRowBits raw.result.modes+bitSize Word.bits raw.result.weights+
    raw.result.precision.bits.length=_
  rw [L.result.copies.size,inp.precision.size,raw.result.precision.size,payload,
    ←w,bitSize_exact _ _ _ (fun k : Word q=>k.size),len]

#print axioms real_mode_record_has_fixed_selected_width
#print axioms actual_shared_control_bits_fit_the_fixed_registers
#print axioms exact_current_native_outputs_from_same_r66_active_tape
end
end J6R68.RecursivePeak