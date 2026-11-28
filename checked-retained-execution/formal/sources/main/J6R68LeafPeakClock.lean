import J6R21LeafClock
import J6R21LeafWidth

/-! Exact selected strict depth-first cuts of the real leaf clock. A
right descent must keep the actual left-subcall result; it is never
replaced by an arbitrary block or by a count of assignments. This
does not price the code behind the per-complete-assignment reader. -/
namespace J6R68.LeafPeak
open AOracleMachineTime A1R10 A1R12 J6R21Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5200000
set_option Elab.async false

theorem encoded_blocks_width {p ell : ℕ} {fw : List (A1R10.Word p)}
    (held : List (UVBlock fw ell)) :
    (held.flatMap leafPayload).length=held.length*(ell*(fw.length*p)) := by
  induction held with
  | nil => simp only [List.flatMap_nil,List.length_nil,Nat.zero_mul]
  | cons b bs ih =>
    rw [List.flatMap_cons,List.length_append,leaf_payload_width,ih,List.length_cons,Nat.succ_mul]
    exact Nat.add_comm _ _

/-- The legal call-stack cut relation for clockDFS starting at an
empty reverse Boolean tape. At a right child the left operand is
the exact already completed sibling. -/
inductive ClockCut {p ell : ℕ} {fw : List (A1R10.Word p)} (hp : 0<p)
    (read : List Bool→Meter (UVBlock fw ell)) (whole : List Unit) :
    List Unit→List Bool→List (UVBlock fw ell)→Prop where
  | start : ClockCut hp read whole whole [] []
  | left {more : List Unit} {rev : List Bool} {lefts : List (UVBlock fw ell)}
      (atNode : ClockCut hp read whole (()::more) rev lefts) :
      ClockCut hp read whole more (false::rev) lefts
  | right {more : List Unit} {rev : List Bool} {lefts : List (UVBlock fw ell)}
      (atNode : ClockCut hp read whole (()::more) rev lefts) :
      ClockCut hp read whole more (true::rev)
        ((clockDFS hp read more (false::rev)).result::lefts)

theorem clock_cut_has_actual_depth_and_held_lefts
    {p ell : ℕ} {fw : List (A1R10.Word p)} {hp : 0<p}
    {read : List Bool→Meter (UVBlock fw ell)} {whole more : List Unit}
    {rev : List Bool} {lefts : List (UVBlock fw ell)}
    (cut : ClockCut hp read whole more rev lefts) :
    more.length+rev.length=whole.length ∧ lefts.length≤rev.length := by
  induction cut with
  | start => simp
  | left atNode ih =>
    simp only [List.length_cons] at ih ⊢
    omega
  | right atNode ih =>
    simp only [List.length_cons] at ih ⊢
    omega

/-- Both operands of the actual binary sum; the third block is
its returned encoded sum. A prefix of that result is no longer
than this full block. This theorem does not measure unlisted
temporaries internal to uvAdd. -/
theorem actual_clock_sum_retains_its_two_children
    {p ell : ℕ} {fw : List (A1R10.Word p)} {hp : 0<p}
    {read : List Bool→Meter (UVBlock fw ell)} {whole more : List Unit}
    {rev : List Bool} {lefts : List (UVBlock fw ell)}
    (cut : ClockCut hp read whole (()::more) rev lefts) :
    let L := clockDFS hp read more (false::rev)
    let R := clockDFS hp read more (true::rev)
    let out := addM hp L R
    clockDFS hp read (()::more) rev=padCost out 4 ∧
      (lefts.flatMap leafPayload).length+
        (leafPayload L.result).length+(leafPayload R.result).length+
          (leafPayload out.result).length+rev.length≤
      (whole.length+3)*(ell*(fw.length*p))+whole.length := by
  have d := clock_cut_has_actual_depth_and_held_lefts cut
  refine ⟨rfl,?_⟩
  rw [encoded_blocks_width,leaf_payload_width,leaf_payload_width,leaf_payload_width]
  have r : rev.length≤whole.length := by omega
  have b : lefts.length≤whole.length := d.2.trans r
  calc
    _ ≤ whole.length*(ell*(fw.length*p))+ell*(fw.length*p)+ell*(fw.length*p)+
          ell*(fw.length*p)+whole.length :=
      Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_right _ b) _) _) _) r
    _ = _ := by ring

/-- At a reached Boolean assignment, preserve its original reverse
spine and the actual forward result of reverseTape. In-progress
reverse accumulators are handled separately below. -/
theorem actual_clock_stop_has_one_forward_tape
    {p ell : ℕ} {fw : List (A1R10.Word p)} {hp : 0<p}
    {read : List Bool→Meter (UVBlock fw ell)} {whole : List Unit}
    {rev : List Bool} {lefts : List (UVBlock fw ell)}
    (cut : ClockCut hp read whole [] rev lefts) :
    let forward := (reverseTape rev []).result
    forward.length=whole.length ∧
    clockDFS hp read [] rev=padCost (read forward) (reverseTape rev []).steps ∧
    (lefts.flatMap leafPayload).length+rev.length+forward.length≤
      whole.length*(ell*(fw.length*p))+2*whole.length := by
  have d := clock_cut_has_actual_depth_and_held_lefts cut
  change 0+rev.length=whole.length ∧ _ at d
  have full : rev.length=whole.length := by omega
  have same : (reverseTape rev []).result.length=whole.length := by
    rw [(reverse_tape_exact rev []).1,List.append_nil,List.length_reverse,full]
  refine ⟨same,rfl,?_⟩
  rw [encoded_blocks_width,same,full]
  have b : lefts.length≤whole.length := d.2.trans_eq full
  have h := Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right (ell*(fw.length*p)) b) whole.length) whole.length
  exact h.trans_eq (by omega)

/-- One real reverseTape traversal consists of a shrinking unread
suffix and the growing reverse prefix; keep the original input
view conservatively even if it is no longer needed. -/
theorem actual_reverse_cut_bounds_the_unread_and_accumulated_bits
    (rev : List Bool) (n : ℕ) :
    let left := rev.drop n
    let acc := (rev.take n).reverse
    (reverseTape left acc).result=(reverseTape rev []).result ∧
      rev.length+left.length+acc.length=2*rev.length := by
  dsimp only
  constructor
  · rw [(reverse_tape_exact _ _).1,(reverse_tape_exact _ _).1,List.append_nil,
      ← List.reverse_append,List.take_append_drop]
  · rw [List.length_reverse]
    have h := congrArg List.length (List.take_append_drop n rev)
    rw [List.length_append] at h
    omega

#print axioms clock_cut_has_actual_depth_and_held_lefts
#print axioms actual_clock_sum_retains_its_two_children
#print axioms actual_clock_stop_has_one_forward_tape
#print axioms actual_reverse_cut_bounds_the_unread_and_accumulated_bits
end J6R68.LeafPeak