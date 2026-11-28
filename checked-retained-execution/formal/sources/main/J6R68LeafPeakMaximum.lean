import J6R68LeafPeakRead

/-! Take the maximum of two different actual stages: a Boolean
subtree sum, and a complete assignment's currently formatted row
read with earlier read outputs still held. The actual command
input tape is counted once outside the maximum. -/
namespace J6R68.LeafPeak
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R21Leaf
open J6R22Active J6R24MeteredRecursion J6R33StatefulArithmeticPage
open J6R50Leaf J6R62Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6100000
set_option Elab.async false

def leafAssignmentMax (n rows uv : ℕ) : ℕ :=
  max ((n+3)*uv+n) ((n+rows)*uv+2*n)

def encodedLeafInputs {key page : ℕ} (clock : List Unit) (cmds : List (ReadCmd key page)) : ℕ :=
  clock.length+(cmds.flatMap leafCommandFields).length

variable {f : ℤ[X]} {p ell key prec tw bw page : ℕ}

def liveReadRegisters (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page) (pre : List (ReadCmd key page)) (cmd : ReadCmd key page)
    (rev : List Bool) (lefts : List (Block F ell)) : ℕ :=
  let assignment := (reverseTape rev []).result
  let pending := pre.map (fun r=>(r.read hf F pos B assignment).result)
  let now := cmd.read hf F pos B assignment
  (lefts.flatMap leafPayload).length+rev.length+assignment.length+
    (pending.flatMap leafPayload).length+(leafPayload now.result).length

def liveAddRegisters {p ell : ℕ} {fw : List (A1R10.Word p)} (hp : 0<p)
    (read : List Bool→Meter (UVBlock fw ell)) (tail : List Unit)
    (rev : List Bool) (lefts : List (UVBlock fw ell)) : ℕ :=
  let l := clockDFS hp read tail (false::rev)
  let r := clockDFS hp read tail (true::rev)
  (lefts.flatMap leafPayload).length+(leafPayload l.result).length+
    (leafPayload r.result).length+(leafPayload (addM hp l r).result).length+rev.length

theorem measured_read_phase_uses_actual_clock_and_entry
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (clock : List Unit) (cmds pre post : List (ReadCmd key page)) (cmd : ReadCmd key page)
    (order : cmds=pre++cmd::post) (formats : ∀ t∈cmds,ReadFormat B clock.length t)
    (rev : List Bool) (held : List (Block F ell))
    (cut : ClockCut F.hp (actualRowQuery hf F pos B cmds) clock [] rev held) :
    (reverseTape rev []).result.length=clock.length ∧ ReadFormat B clock.length cmd ∧
      encodedLeafInputs clock cmds+liveReadRegisters hf F pos B pre cmd rev held≤
        encodedLeafInputs clock cmds+leafAssignmentMax clock.length cmds.length (ell*(F.words.length*p)) := by
  obtain ⟨len,format,space⟩ := same_assignment_and_current_entry_fit_named_leaf_registers
    hf F pos B clock cmds pre post cmd order formats rev held cut
  have narrow : liveReadRegisters hf F pos B pre cmd rev held≤
      (clock.length+cmds.length)*(ell*(F.words.length*p))+2*clock.length := by
    exact Nat.le_of_add_le_add_right (show liveReadRegisters hf F pos B pre cmd rev held+
      (leafCommandFields cmd).length≤_ from space)
  exact ⟨len,format,Nat.add_le_add_left (narrow.trans (Nat.le_max_right _ _)) _⟩

theorem measured_add_phase_has_one_actual_pair_and_result
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (clock tail : List Unit) (cmds : List (ReadCmd key page))
    (rev : List Bool) (held : List (Block F ell))
    (cut : ClockCut F.hp (actualRowQuery hf F pos B cmds) clock (()::tail) rev held) :
    encodedLeafInputs clock cmds+
      liveAddRegisters F.hp (actualRowQuery hf F pos B cmds) tail rev held≤
      encodedLeafInputs clock cmds+leafAssignmentMax clock.length cmds.length (ell*(F.words.length*p)) := by
  have bound : liveAddRegisters F.hp (actualRowQuery hf F pos B cmds) tail rev held≤
      (clock.length+3)*(ell*(F.words.length*p))+clock.length :=
    (actual_clock_sum_retains_its_two_children cut).2
  exact Nat.add_le_add_left (bound.trans (Nat.le_max_left _ _)) _

def liveReverseRegisters {p ell : ℕ} {fw : List (A1R10.Word p)}
    (rev : List Bool) (held : List (UVBlock fw ell)) (i : ℕ) : ℕ :=
  (held.flatMap leafPayload).length+
    (rev.length+(rev.drop i).length+((rev.take i).reverse).length)

theorem measured_reverse_phase_retains_only_these_named_views
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (clock : List Unit) (cmds : List (ReadCmd key page))
    (rev : List Bool) (held : List (Block F ell))
    (cut : ClockCut F.hp (actualRowQuery hf F pos B cmds) clock [] rev held) (i : ℕ) :
    encodedLeafInputs clock cmds+liveReverseRegisters rev held i≤
      encodedLeafInputs clock cmds+leafAssignmentMax clock.length cmds.length (ell*(F.words.length*p)) := by
  have depth := clock_cut_has_actual_depth_and_held_lefts cut
  have full : rev.length=clock.length := by simpa only [List.length_nil,Nat.zero_add] using depth.1
  have hc : held.length≤clock.length := depth.2.trans_eq full
  have raw := (actual_reverse_cut_bounds_the_unread_and_accumulated_bits rev i).2
  have own : liveReverseRegisters rev held i≤(clock.length+cmds.length)*(ell*(F.words.length*p))+2*clock.length := by
    unfold liveReverseRegisters
    rw [encoded_blocks_width,raw,full]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (hc.trans (Nat.le_add_right _ _))) _
  exact Nat.add_le_add_left (own.trans (Nat.le_max_right _ _)) _

#print axioms measured_reverse_phase_retains_only_these_named_views

#print axioms measured_read_phase_uses_actual_clock_and_entry
#print axioms measured_add_phase_has_one_actual_pair_and_result
end J6R68.LeafPeak