
import J6R52PeakReaderDefs
import J6R49DFSReachEvents
import J6R49DFSVisitMath
import J6R49LivePeak

/-! Actual selected mode prefix and group accumulator for the
online reader, not the old prepared callback. The mode trace is
proof data. The continuation is exactly the originally paid probe. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R17ModeTape J6R24MeteredRecursion J6R25PreparedSupply
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits
open J6R51Online

set_option autoImplicit false
set_option maxRecDepth 3550
set_option maxHeartbeats 18500000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def SawOnlineMode (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c)
    (w : (P).Slot c) (o : NativeSuspension (C:=C) (sel:=sel) c) : Prop :=
  let d := ready_reachable cfg sel p.reached T.rootStable w.property
  let t := w.val.1
  let z := w.val.2.1
  let β := w.val.2.2.1
  let g := w.val.2.2.2
  let F := T.bank (registerPrecision S c t) (register_positive d t)
  let I := ((activeAt M p w.property).result.tape t).tape.result
  let read := readAt M retire initial p w.property t z
  ∃ (size : q≤uniformWidth s C) (started now : Pending q I.words.length)
    (outer inner : Block F ell) (fee feeM : ℕ)
    (raw : List (J6R15ModeCost.Word q)) (next : J6R15ModeCost.State q) (left : List (Fin 64)),
    (startingCursor I M.modeWidth).result=some started ∧
    ModePrefix (modeUpdate F I T.vPositive read) started
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I M.modeWidth).steps)
        now outer fee ∧
    ∃ emit : now.pulse.result=.emit raw next,
      decodeAt I raw=some β ∧
      GroupPrefix F.hp (read β) (oneM F.hp F.sizePos T.vPositive).result
        (oneM F.hp F.sizePos T.vPositive).steps (g::left) inner feeM ∧
      o=⟨d,t,q,size,I,now.state,now.valid,F,outer,inner⟩ ∧
      (let mul := mulM F.hp ⟨inner,0⟩ (read β g)
       let prod := productCursor F.hp (read β) left mul.result (feeM+mul.steps)
       let sum := addM F.hp ⟨outer,0⟩ prod
       let tail := modeDrain (modeUpdate F I T.vPositive read) (now.tail emit) sum.result
         (fee+now.pulse.steps+sum.steps)
       runProbe F I M.modeWidth T.vPositive read=⟨tail.result.1,tail.steps⟩)

theorem slot_is_literal_online_address (p : Path sel r c) (w : (P).Slot c) :
    let d := ready_reachable cfg sel p.reached T.rootStable w.property
    w=addressed (sel:=sel) d w.val.1 w.val.2.1 w.val.2.2.1 w.val.2.2.2 := by
  dsimp only
  apply Subtype.ext
  change w.val=⟨w.val.1,w.val.2.1,w.val.2.2.1,w.val.2.2.2⟩
  obtain ⟨t,z,β,g⟩ := w.val
  rfl

theorem each_online_slot_has_its_real_mode_event (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (fits : q≤uniformWidth s C)
    (p : Path sel r c) (w : (P).Slot c) :
    ∃ o : NativeSuspension (C:=C) (sel:=sel) c,SawOnlineMode M retire initial p w o := by
  let a := w.property
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let t := w.val.1
  let z := w.val.2.1
  let β := w.val.2.2.1
  let g := w.val.2.2.2
  let I := ((activeAt M p a).result.tape t).tape.result
  let F := T.bank (registerPrecision S c t) (register_positive d t)
  let read := readAt M retire initial p a t z
  let k := vectorKey sel d t I β
  have onTape : k∈tupleSpec I := by
    apply (native_tuple_iff sel d t I.modes I.nodup I.allModes k).mpr
    exact ⟨β,rfl,fun _ e=>vector_key_inj sel d t I e⟩
  obtain ⟨started,start,_,trace⟩ := starting_cursor_exact I M.modeWidth
  let init := zeroM (ell:=ell) (f:=F.words) F.hp
  obtain ⟨now,outer,fee,v,next,proceeded,emit,exactWords⟩ :=
    every_transcript_row_is_visited (modeUpdate F I T.vPositive read) (tupleSpec I)
      k started init.result (init.steps+(startingCursor I M.modeWidth).steps) trace onTape
  have bytes : k.map (J6R15ModeCost.word (q:=q))=v := by
    rw [←exactWords,canonical_tuple_words]
  have decoded : decodeAt I v=some β := by
    rw [←bytes,decode_canonical_mode_words I β (actual_legal_coordinates_fit I β)]
  let initProduct := oneM F.hp F.sizePos T.vPositive
  obtain ⟨left,inner,feeM,pref⟩ := every_left_group_is_visited F.hp (read β)
    initProduct.result initProduct.steps g
  refine ⟨⟨d,t,q,fits,I,now.state,now.valid,F,outer,inner⟩,?_⟩
  exact ⟨fits,started,now,outer,inner,fee,feeM,v,next,left,start,proceeded,emit,decoded,pref,rfl,
    probe_halts_after_actual_child F I M.modeWidth T.vPositive read started start now outer fee
      proceeded v next emit β decoded g left inner feeM pref⟩

#print axioms slot_is_literal_online_address
#print axioms each_online_slot_has_its_real_mode_event
end J6R52Peak
