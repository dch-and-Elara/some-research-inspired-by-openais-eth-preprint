import J6R49DFSPathPeak
import J6R49DFSReachEvents

/-! Coverage of the suspension trace: each literal Plan slot is reached
through an actual emission of its exact legal tuple and the matching
left-product prefix. Consequently the peak theorem applies to every
typed occurrence path with a represented chronological view, not a
vacuous subset of guessed paths. The view is proof data only. -/
namespace J6R49DFS
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R17ModeTape J6R24MeteredRecursion J6R25PreparedSupply
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 12500000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

theorem each_actual_slot_has_emission (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (qFit : q≤uniformWidth s C)
    (p : Path sel r c) (w : (Plan sel).Slot c) :
    ∃ obs : NativeSuspension (C:=C) (sel:=sel) c,ActualModeEvent R retire initial p w obs := by
  let a := w.property
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let t := w.val.1
  let z := w.val.2.1
  let β := w.val.2.2.1
  let g := w.val.2.2.2
  let I := ((R.active p a).tape t).tape.result
  let F := T.bank (registerPrecision S c t) (register_positive d t)
  let read := actualChildRead R retire p a (stackBank R.births initial p) t z
  let key := vectorKey sel d t I β
  have onTape : key∈tupleSpec I := by
    apply (native_tuple_iff sel d t I.modes I.nodup I.allModes key).mpr
    exact ⟨β,rfl,fun other h=>vector_key_inj sel d t I h⟩
  obtain ⟨start,starts,_,trace⟩ := starting_cursor_exact I R.modeWidth
  let init := zeroM (ell:=ell) (f:=F.words) F.hp
  obtain ⟨now,outer,fee,v,next,proceeded,emit,exactWords⟩ :=
    every_transcript_row_is_visited (modeUpdate F I T.vPositive read) (tupleSpec I)
      key start init.result (init.steps+(startingCursor I R.modeWidth).steps) trace onTape
  have bytes : key.map (J6R15ModeCost.word (q:=q))=v := by
    rw [←exactWords,canonical_tuple_words]
  have decode : decodeAt I v=some β := by
    rw [←bytes,decode_canonical_mode_words I β (actual_legal_coordinates_fit I β)]
  let initProduct := oneM F.hp F.sizePos T.vPositive
  obtain ⟨left,inner,k,pref⟩ := every_left_group_is_visited F.hp (read β) initProduct.result initProduct.steps g
  have addressSame : w=addressed (sel:=sel) d t z β g := by
    apply Subtype.ext
    change w.val=⟨w.val.1,w.val.2.1,w.val.2.2.1,w.val.2.2.2⟩
    obtain ⟨t₀,z₀,β₀,g₀⟩ := w.val
    rfl
  refine ⟨⟨d,t,q,qFit,I,now.state,now.valid,F,outer,inner⟩,?_⟩
  exact ⟨a,t,z,qFit,start,now,outer,inner,fee,k,v,next,β,g,left,
    starts,proceeded,emit,decode,pref,addressSame,rfl⟩

theorem each_actual_path_has_stream_trace (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (qFit : q≤uniformWidth s C) (p : Path sel r c) :
    ∃ b,RecursiveModeTrace R retire initial p b := by
  induction p with
  | root => exact ⟨0,.root⟩
  | step p w ih =>
    obtain ⟨b,trace⟩ := ih
    obtain ⟨o,event⟩ := each_actual_slot_has_emission R retire initial qFit p w
    exact ⟨b+o.measure.bits,.push trace w o event⟩

theorem combined_stream_selected_fields_peak (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L)
    (rootDepth : r.depth=0) (rootPrec : r.prec≤C*s) (p : Path sel r c) (b : ℕ)
    (trace : RecursiveModeTrace R retire initial p b)
    (pageBound : ℕ) (rows : AllExactPages R.births)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (path : Path sel r x) (w : (Plan sel).Slot x),
      let e := (R.births path w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound) :
    residentAtlasBits (stackBank R.births initial p)+b≤
      residentAtlasBits initial+((96*r.edges)/29)*(page+pageBound)+
        (pathLimit s C*frameBase (uniformWidth s C) (rosterSize s C)+
          (32*r.edges/29)*frameSlope s C ell f.natDegree) :=
  Nat.add_le_add (scoped_generated_literal_page_bits R.births initial pageBound rows bits p)
    (real_recursive_stream_mode_peak R retire initial p b trace rootDepth rootPrec)

#print axioms each_actual_slot_has_emission
#print axioms each_actual_path_has_stream_trace
#print axioms combined_stream_selected_fields_peak
end J6R49DFS
