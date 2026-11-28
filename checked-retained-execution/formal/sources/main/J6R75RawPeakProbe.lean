import J6R57LiveSpaceCachedMode
import J6R68HermiteWeightScratchRawCore
import J6R68ActiveInputsSweepLedger
import J6R72SameRunRawScope

/-! The mode cursor is matched directly inside the raw emitted row.
No comparison of whole Meters or of the legacy active supplier is used
to infer which operands are retained at this probe. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R17ModeTape J6R24MeteredRecursion J6R25PreparedSupply J6R9Recursive
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits
open J6R51Online J6R52Peak J6R53PeakAddon J6R68ActiveInputs.Sweep J6R68.HermiteWeightScratch
open J6R63Active J6R62ActivePrep J6R66Active J6R72SameRunRawScope

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4500
set_option maxSynthPendingDepth 12

noncomputable section
variable {f : ℤ[X]} {ell s C q : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {bank : Bank f}

def SawEmittedProbe
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (D : Schedule sel d bank q) (hq : 0<q) (hv : 0<ell)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (x : D.EmitRow) (z : Probe S c) (β : NativeMenu (N sel) c (D.tag x)) (g : Fin 64)
    (o : NativeSuspension (C:=C) (sel:=sel) c) : Prop :=
  let t := D.tag x
  let F := bank (registerPrecision S c t) (register_positive d t)
  let I := (D.fetch x).tape.result
  let read := child t z
  ∃ (size : q≤uniformWidth s C) (started now : Pending q I.words.length)
    (outer inner : Block F ell) (fee feeM : ℕ)
    (raw : List (J6R15ModeCost.Word q)) (next : J6R15ModeCost.State q) (left : List (Fin 64)),
    (startingCursor I hq).result=some started ∧
    ModePrefix (modeUpdate F I hv read) started
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I hq).steps)
        now outer fee ∧
    ∃ emit : now.pulse.result=.emit raw next,
      decodeAt I raw=some β ∧
      GroupPrefix F.hp (read β) (oneM F.hp F.sizePos hv).result
        (oneM F.hp F.sizePos hv).steps (g::left) inner feeM ∧
      o=⟨d,t,q,size,I,now.state,now.valid,F,outer,inner⟩ ∧
      (let mul := mulM F.hp ⟨inner,0⟩ (read β g)
       let prod := productCursor F.hp (read β) left mul.result (feeM+mul.steps)
       let sum := addM F.hp ⟨outer,0⟩ prod
       let tail := modeDrain (modeUpdate F I hv read) (now.tail emit) sum.result
         (fee+now.pulse.steps+sum.steps)
       runProbe F I hq hv read=⟨tail.result.1,tail.steps⟩)

theorem every_emitted_row_address_has_its_native_cursor_and_group_cut
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (D : Schedule sel d bank q)
    (fits : q≤uniformWidth s C) (hq : 0<q) (hv : 0<ell)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (x : D.EmitRow) (z : Probe S c) (β : NativeMenu (N sel) c (D.tag x)) (g : Fin 64) :
    ∃ o : NativeSuspension (C:=C) (sel:=sel) c,SawEmittedProbe d D hq hv child x z β g o := by
  let t := D.tag x
  let I := (D.fetch x).tape.result
  let F := bank (registerPrecision S c t) (register_positive d t)
  let read := child t z
  let k := vectorKey sel d t I β
  have onTape : k∈tupleSpec I := by
    apply (native_tuple_iff sel d t I.modes I.nodup I.allModes k).mpr
    exact ⟨β,rfl,fun _ e=>vector_key_inj sel d t I e⟩
  obtain ⟨started,start,_,trace⟩ := starting_cursor_exact I hq
  let init := zeroM (ell:=ell) (f:=F.words) F.hp
  obtain ⟨now,outer,fee,v,next,proceeded,emit,exactWords⟩ :=
    every_transcript_row_is_visited (modeUpdate F I hv read) (tupleSpec I)
      k started init.result (init.steps+(startingCursor I hq).steps) trace onTape
  have bytes : k.map (J6R15ModeCost.word (q:=q))=v := by
    rw [←exactWords,canonical_tuple_words]
  have decoded : decodeAt I v=some β := by
    rw [←bytes,decode_canonical_mode_words I β (actual_legal_coordinates_fit I β)]
  let initProduct := oneM F.hp F.sizePos hv
  obtain ⟨left,inner,feeM,pref⟩ := every_left_group_is_visited F.hp (read β)
    initProduct.result initProduct.steps g
  refine ⟨⟨d,t,q,fits,I,now.state,now.valid,F,outer,inner⟩,?_⟩
  exact ⟨fits,started,now,outer,inner,fee,feeM,v,next,left,start,proceeded,emit,decoded,pref,rfl,
    probe_halts_after_actual_child F I hq hv read started start now outer fee
      proceeded v next emit β decoded g left inner feeM pref⟩

#print axioms every_emitted_row_address_has_its_native_cursor_and_group_cut
end
end J6R75RawPeak
