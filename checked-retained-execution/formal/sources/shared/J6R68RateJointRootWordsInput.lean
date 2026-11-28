import J6R68RateJointRootWordsReplay
import J6R57ScopeFeeAtlas

/-! A checked first-template handle supplies source bytes, not arbitrary
nested producer fees. Replay the exact selected NativeJob and ActiveWords
and their physical roster once. No gate/page atlas producer runs here. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R26DescriptorTree J6R33GeneratedChildSite J6R53OldOwner J6R34RootAtlas
open J6R50SourceProducer J6R32ChildResidentTransfer J6R17ModeTape J6R57ScopeFee
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6ActiveSchedule
open J6R10Repack J6R30ProducedGateRegistry

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4200
set_option maxHeartbeats 25000000
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => ((SP).levelBits v.parent.depth)
local notation "P" => (registerPrecision SP v.parent v.centerAt)
local notation "D" => (ticketReady T v)
local notation "I₀" => (centerIndex (ticketReady T v) v.centerAt)

theorem transported_chart_indices {n : ℕ} {x y : ChildResidents A n}
    (H : ResidentReceipt (packing sel D) I₀ P x) (e : x=y) :
    let K := (e ▸ H : ResidentReceipt (packing sel D) I₀ P y)
    K.edges=H.edges ∧ K.modes=H.modes := by
  subst y
  exact ⟨rfl,rfl⟩

def replayFirstInput (I : OccurrenceInput T v key prec tw bw page)
    (issued : Meter (Word key)) : OccurrenceInput T v key prec tw bw page :=
  let n := copyFirstNative I.native.result
  let r := copyResidentFields I.physical.result
  let w := copyActiveFields I.words.result
  let f := copyModulus I.fw
  have NE := congrArg Meter.result (copy_first_native_exact I.native.result)
  have RE := congrArg Meter.result (copy_resident_fields_exact I.physical.result)
  have WE := congrArg Meter.result (copy_active_fields_exact I.words.result)
  have FE := congrArg Meter.result (copy_modulus_exact I.fw)
  let G : ResidentReceipt (packing sel D) I₀ P r.result := RE.symm ▸ I.geometry
  have modes : G.modes=I.geometry.modes := (transported_chart_indices (T:=T) (v:=v) I.geometry RE.symm).2
  let X : ActiveWords f.result (I.q+1) tw bw :=
    ⟨w.result.context,w.result.axis,w.result.group,w.result.exponents,
      ⟨w.result.coordinates.val,w.result.coordinates.property.trans (congrArg List.length FE).symm⟩⟩
  { I with
    issued := issued
    native := n
    fw := f.result
    hOld := FE.symm ▸ I.hOld
    hMod := FE.symm ▸ I.hMod
    words := ⟨X,w.steps+f.steps+4⟩
    physical := r
    geometry := G
    group := (congrArg ActiveWords.group WE).trans (I.group.trans
      (congrArg NativeJob.gWord NE).symm)
    clock := (congrArg (fun a=>a.axis.length) WE).trans I.clock
    centre := (congrArg (fun a=>a.context.center) WE).trans I.centre
    codeExact := (congrArg (fun a=>a.context.codeWidth.val) WE).trans I.codeExact
    codeFit := by rw [modes]; exact I.codeFit
    acted := by
      change w.result.exponents.map Word.val = _
      rw [WE,modes]
      exact I.acted
    probe := (congrArg (fun a=>a.coordinates.val) WE).trans I.probe }

theorem replay_first_input_has_the_same_selected_source
    (I : OccurrenceInput T v key prec tw bw page) (issued : Meter (Word key)) :
    let R := replayFirstInput I issued
    R.issued=issued ∧ HEq R.native.result I.native.result ∧ R.fw=I.fw ∧
      HEq R.physical.result I.physical.result ∧ R.geometry.edges=I.geometry.edges ∧
      R.geometry.modes=I.geometry.modes ∧ R.words.result.context=I.words.result.context ∧
      R.words.result.axis=I.words.result.axis ∧ R.words.result.group=I.words.result.group ∧
      HEq R.words.result.exponents I.words.result.exponents ∧
      R.words.result.coordinates.val=I.words.result.coordinates.val := by
  have n := congrArg Meter.result (copy_first_native_exact I.native.result)
  have f := congrArg Meter.result (copy_modulus_exact I.fw)
  have r := congrArg Meter.result (copy_resident_fields_exact I.physical.result)
  obtain ⟨e,m⟩ := transported_chart_indices (T:=T) (v:=v) I.geometry r.symm
  have w := congrArg Meter.result (copy_active_fields_exact I.words.result)
  exact ⟨rfl,heq_of_eq n,f,heq_of_eq r,e,m,congrArg ActiveWords.context w,congrArg ActiveWords.axis w,
    congrArg ActiveWords.group w,heq_of_eq (congrArg ActiveWords.exponents w),
    congrArg (fun a=>a.coordinates.val) w⟩

def firstReplayTariff (I : OccurrenceInput T v key prec tw bw page) (issueFee : ℕ) : ℕ :=
  issueFee+nativeFieldsFee I.tc I.tz I.tm I.dep prec+
    chartResidentFee A I.q I.geometry.edges.length (packing sel D).copies I.geometry.modes.length+
    activeFieldsFee (I.q+1) tw bw (I₀).val (4*Nat.clog 2 s) I.geometry.modes.length+
    (3+(3*P+5)*(4*Nat.clog 2 s))+8

theorem actual_issued_frame_width (I : OccurrenceInput T v key prec tw bw page) :
    I.fw.length=4*Nat.clog 2 s :=
  let F : Frame f P := ⟨register_positive D v.centerAt,I.fw,I.hOld,I.hMod⟩
  (F.natDegree hf).trans cfg.coefficient

theorem true_first_replayed_native_fields_fee
    (I : OccurrenceInput T v key prec tw bw page) (issued : Meter (Word key)) :
    measuredWordProducers (replayFirstInput I issued)=firstReplayTariff I issued.steps := by
  have hb := congrArg List.length I.acted
  have e : I.words.result.exponents.length=I.geometry.modes.length := by
    simpa only [List.length_map] using hb
  have N := congrArg Meter.steps (copy_first_native_exact I.native.result)
  have R := congrArg Meter.steps (copy_resident_fields_from_exact_geometry I.geometry)
  have C := congrArg Meter.steps (copy_active_fields_exact I.words.result)
  have F := congrArg Meter.steps (copy_modulus_exact I.fw)
  simp only [I.clock,actual_issued_frame_width I,e] at C
  rw [actual_issued_frame_width I] at F
  change issued.steps+((copyFirstNative I.native.result).steps+(copyResidentFields I.physical.result).steps+
    ((copyActiveFields I.words.result).steps+(copyModulus I.fw).steps+4)+4)=_
  unfold firstReplayTariff
  rw [N,R,C,F]
  dsimp only
  omega

#print axioms transported_chart_indices
#print axioms replay_first_input_has_the_same_selected_source
#print axioms actual_issued_frame_width
#print axioms true_first_replayed_native_fields_fee
end
end J6R68RateJoint.RootWords

