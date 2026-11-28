import J6R50LeafOnline
import J6R68LeafPeakMaximum

/-! The original terminal loop on the actual RawTape. The erased
command list is only a view of the same row meanings and selected
fields, not an additional physical list allocated by runTape. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R48Leaf J6R21Leaf J6R21Ancestor J6R50Leaf J6R62Leaf
open J6R33StatefulArithmeticPage J6R68.LeafPeak J6R9Recursive

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4200
set_option maxHeartbeats 4500000

noncomputable section
variable {f : ℤ[X]} {ell key prec tw bw page : ℕ} {c : Call (PhysicalHost f ell)}
local notation "L" => (PageBank f ell key prec tw bw page)

def rawLeafCommands (D : RawTape c key page) : List (ReadCmd key page) :=
  D.rows.map (fun r=>eraseCode r.2)

theorem actual_raw_leaf_command_formats
    (D : RawTape c key page) (B : L) (formats : HasResidentFormat D B) :
    ∀ cmd∈rawLeafCommands D,ReadFormat B D.clock.length cmd := by
  intro cmd mem
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
  rw [D.clockExact]
  have valid := formats r hr
  cases code : r.2 with
  | original b g => simp only [eraseCode,ReadFormat]
  | generated id pg dep wires => simpa only [code,eraseCode,ReadFormat] using valid

def selectedTerminalRoom {p : ℕ} (F : Frame f p) (clock : List Unit)
    (rows : List (ReadCmd key page)) : ℕ :=
  encodedLeafInputs clock rows+leafAssignmentMax clock.length rows.length (ell*(F.words.length*p))

def SelectedTerminalCuts
    (hf : f.Monic) (F : Frame f c.prec) (pos : 0<ell) (B : L)
    (D : RawTape c key page) (resident roof : ℕ) : Prop :=
  let rows := rawLeafCommands D
  let clk := D.clock
  let room := roof+(selectedTerminalRoom (ell:=ell) F clk rows)
  let read := actualRowQuery hf F pos B rows
  (∀ cmd∈rows,ReadFormat B clk.length cmd) ∧
  (∀ (pre post : List (ReadCmd key page)) (cmd : ReadCmd key page) (rev : List Bool)
       (lefts : List (Block F ell)),
    rows=pre++cmd::post → ClockCut F.hp read clk [] rev lefts →
    resident+(encodedLeafInputs clk rows+liveReadRegisters hf F pos B pre cmd rev lefts)≤room) ∧
  (∀ (rev : List Bool) (lefts : List (Block F ell)),
    ClockCut F.hp read clk [] rev lefts → ∀ j,
    resident+(encodedLeafInputs clk rows+liveReverseRegisters rev lefts j)≤room) ∧
  (∀ (tail : List Unit) (rev : List Bool) (lefts : List (Block F ell)),
    ClockCut F.hp read clk (()::tail) rev lefts →
    resident+(encodedLeafInputs clk rows+liveAddRegisters F.hp read tail rev lefts)≤room)

theorem true_raw_terminal_tape_has_selected_clock_cuts
    (hf : f.Monic) (F : Frame f c.prec) (pos : 0<ell) (B : L)
    (D : RawTape c key page) (formats : HasResidentFormat D B)
    (resident roof : ℕ) (fit : resident≤roof) :
    runTape D hf F pos B=runRows hf F pos B D.clock (rawLeafCommands D) ∧
    SelectedTerminalCuts hf F pos B D resident roof := by
  let rows := rawLeafCommands D
  let clk := D.clock
  let read := actualRowQuery hf F pos B rows
  have fmt := actual_raw_leaf_command_formats D B formats
  refine ⟨(run_rows_is_raw hf F pos B D).symm,fmt,?_,?_,?_⟩
  · intro pre post cmd rev lefts order cut
    exact Nat.add_le_add fit (measured_read_phase_uses_actual_clock_and_entry hf F pos B
      clk rows pre post cmd order fmt rev lefts cut).2.2
  · intro rev lefts cut j
    exact Nat.add_le_add fit (measured_reverse_phase_retains_only_these_named_views hf F pos B clk
      rows rev lefts cut j)
  · intro tail rev lefts cut
    exact Nat.add_le_add fit (measured_add_phase_has_one_actual_pair_and_result hf F pos B clk
      tail rows rev lefts cut)

#print axioms actual_raw_leaf_command_formats
#print axioms true_raw_terminal_tape_has_selected_clock_cuts
end
end J6R75RawPeak
