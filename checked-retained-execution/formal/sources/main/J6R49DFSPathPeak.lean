import J6R49DFSTypedVisit

/-! A proof-side history of actual mode suspensions on the original
dependent occurrence stack. A predecessor event has to come from
this centre's real cursor and group accumulators, and its exact
decoded tuple and next group must be the slot followed by the path.
No all-invocations history is retained by nativeStream. -/
namespace J6R49DFS
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49LiveBits

set_option autoImplicit false
set_option linter.unusedSectionVars false
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

def ActualModeEvent (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c)
    (w : (Plan sel).Slot c) (o : NativeSuspension (C:=C) (sel:=sel) c) : Prop :=
  ∃ (eligible : (S).cutoff<c.edges) (t : Center S c) (z : Probe S c),
    let d := ready_reachable cfg sel p.reached T.rootStable eligible
    let F := T.bank (registerPrecision S c t) (register_positive d t)
    let I := ((R.active p eligible).tape t).tape.result
    let read := actualChildRead R retire p eligible (stackBank R.births initial p) t z
    ∃ (qFit : q≤uniformWidth s C) (firstState now : Pending q I.words.length)
       (outer inner : Block F ell) (fee feeM : ℕ)
       (v : List (J6R15ModeCost.Word q)) (next : J6R15ModeCost.State q)
       (β : NativeMenu (N sel) c t) (g : Fin 64) (left : List (Fin 64)),
      (startingCursor I R.modeWidth).result=some firstState ∧
      ModePrefix (modeUpdate F I T.vPositive read) firstState
        (zeroM (ell:=ell) (f:=F.words) F.hp).result
        ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I R.modeWidth).steps) now outer fee ∧
      now.pulse.result=.emit v next ∧ decodeAt I v=some β ∧
      GroupPrefix F.hp (read β) (oneM F.hp F.sizePos T.vPositive).result
        (oneM F.hp F.sizePos T.vPositive).steps (g::left) inner feeM ∧
      w=addressed (sel:=sel) d t z β g ∧
      o=⟨d,t,q,qFit,I,now.state,now.valid,F,outer,inner⟩

theorem real_mode_event_bound (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c)
    (w : (Plan sel).Slot c) (o : NativeSuspension (C:=C) (sel:=sel) c)
    (seen : ActualModeEvent R retire initial p w o) (d₀ : r.depth=0) (bp : r.prec≤C*s) :
    o.measure.bits≤frameBase (uniformWidth s C) (rosterSize s C)+c.edges*frameSlope s C ell f.natDegree := by
  rcases seen with ⟨ac,t,z,qFit,firstState,now,outer,inner,fee,feeM,v,next,β,g,left,
    start,prev,emit,code,groups,_,observed⟩
  let d := ready_reachable cfg sel p.reached T.rootStable ac
  let F := T.bank (registerPrecision S c t) (register_positive d t)
  let I := ((R.active p ac).tape t).tape.result
  have flds := literal_emission_fields_and_continuation cfg T.rootStable d₀ bp p d t F hf
    I R.modeWidth qFit T.vPositive
    (actualChildRead R retire p ac (stackBank R.births initial p) t z)
    firstState start now outer fee prev v next emit β code g left inner feeM groups
  rw [observed]
  exact flds.1

inductive RecursiveModeTrace (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ → Prop where
  | root : RecursiveModeTrace R retire initial (Path.root : Path sel r r) 0
  | push {x : Call (PhysicalHost f ell)} {p : Path sel r x} {b : ℕ}
      (earlier : RecursiveModeTrace R retire initial p b)
      (w : (Plan sel).Slot x) (o : NativeSuspension (C:=C) (sel:=sel) x)
      (seen : ActualModeEvent R retire initial p w o) :
      RecursiveModeTrace R retire initial (.step p w) (b+o.measure.bits)

/-- The genuine current ancestry only. The bound counts the selected
suspended mode fields, then independently adds the already checked
atlas bound. It does not meter more memory merely because some
non-mode interpolation scratch might be allocated in this process. -/
theorem real_recursive_stream_mode_peak (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c) (b : ℕ)
    (trace : RecursiveModeTrace R retire initial p b) (d₀ : r.depth=0) (bp : r.prec≤C*s) :
    b≤pathLimit s C*frameBase (uniformWidth s C) (rosterSize s C)+
      (32*r.edges/29)*frameSlope s C ell f.natDegree := by
  let B := frameBase (uniformWidth s C) (rosterSize s C)
  let K := frameSlope s C ell f.natDegree
  have tracking : b + c.edges*K ≤ moves p * B + (edgeStack p).sum*K := by
    induction trace with
    | root => simp [moves,edgeStack]
    | @push x p b earlier w o seen ih =>
      have actual := real_mode_event_bound R retire initial p w o seen d₀ bp
      change o.measure.bits≤B+x.edges*K at actual
      simp only [moves,edgeStack,List.sum_append,List.sum_cons,List.sum_nil,
        Nat.add_zero,Nat.add_mul]
      omega
  have depth : moves p≤pathLimit s C := by
    have d := printed_stack_level_bound cfg T.rootStable d₀ p
    have H := (stack_exact_depth p).2
    omega
  have sum : (edgeStack p).sum ≤ (32*r.edges)/29 := by
    have e := edgeStack_geometric p
    omega
  exact (Nat.le_add_right _ _).trans (tracking.trans
    (Nat.add_le_add (Nat.mul_le_mul_right _ depth) (Nat.mul_le_mul_right _ sum)))

#print axioms real_mode_event_bound
#print axioms real_recursive_stream_mode_peak
end J6R49DFS
