import J6R75RawPeakPacketRetention

/-! A literal stopped clock and each of its actual read/add/reverse
and formatted packet region cuts, with one fixed ancestor charge. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R12
open J6R18ChildWrite J6R19Retained J6R20Ancestor J6R21Ancestor J6R21Leaf
open J6R22Active J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R33StatefulArithmeticPage J6R48Leaf J6R50Leaf J6R62Leaf
open J6R68.LeafPeak J6R68.LeafPeak.Packet J6R50NonModeScratch

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4350
set_option maxHeartbeats 7500000

noncomputable section
variable {f : ℤ[X]} {ell p key prec tw bw page : ℕ}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Cmd" => (ReadCmd key page)

def PacketRetentionCut
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : L)
    (clk : List Unit) (rows pre _post : List Cmd)
    (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page) (d : ℕ) (wires : List WireRead)
    (rev : List Bool) (lefts : List (Block F ell)) (resident roof : ℕ) : Prop :=
    ∃ Q : LivePageHit B id pg,
      let bits := (reverseTape rev []).result
      let kept := resident+(encodedLeafInputs clk rows+pendingLeafWords hf F pos B pre rev lefts)
      let current := (.packet id pg d wires : Cmd).read hf F pos B bits
      let stored := Q.routeBits d wires bits+Q.tableSize pos d wires bits
      let room := roof+selectedTerminalRoom (ell:=ell) F clk rows+
        max (Q.routeRoom wires+Q.tableRoom+Q.choiceRoom) (Q.W+ell*(F.words.length*p))+
        (Q.routeRoom wires+Q.tableRoom)+13*Q.W
      current.result=(Q.delivered hf F pos d wires bits).result ∧
      (∀ j,kept+stored+((leafPayload (Q.createdValue pos d wires bits).result).length+
        ((leafPayload (Q.delivered hf F pos d wires bits).result).take j).length)≤room) ∧
      (∀ (preU : List (UBlock Q.S.old)) (head : UBlock Q.S.old) (tail : List (UBlock Q.S.old)),
        (Q.coefficient pos d wires bits).result.val=preU++head::tail →
        let a := (Q.coefficient pos d wires bits).result
        let b := (Q.moments pos d wires bits).result
        let result := (Q.createdValue pos d wires bits).result
        let scratch := (encodeArrays scalarPayload (combineArrays (uGates Q.S.pPos Q.S.old) head tail b.val)).length
        result.val=(convolve (uGates Q.S.pPos Q.S.old) a.val b.val).result.drop ell ∧
        kept+stored+((leafPayload a).length+(leafPayload b).length+scratch+(leafPayload result).length)≤room)

def SelectedStopClockCuts
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : L)
    (clk : List Unit) (rows : List Cmd) (resident roof : ℕ) : Prop :=
  let cutRoom := roof+selectedTerminalRoom (ell:=ell) F clk rows
  let read := actualRowQuery hf F pos B rows
  (∀ row∈rows,ReadFormat B clk.length row) ∧
  (∀ (pre post : List Cmd) (cmd : Cmd) (rev : List Bool) (lefts : List (Block F ell)),
    rows=pre++cmd::post → ClockCut F.hp read clk [] rev lefts →
    resident+(encodedLeafInputs clk rows+liveReadRegisters hf F pos B pre cmd rev lefts)≤cutRoom) ∧
  (∀ (rev : List Bool) (lefts : List (Block F ell)),
    ClockCut F.hp read clk [] rev lefts → ∀ j,
    resident+(encodedLeafInputs clk rows+liveReverseRegisters rev lefts j)≤cutRoom) ∧
  (∀ (tail : List Unit) (rev : List Bool) (lefts : List (Block F ell)),
    ClockCut F.hp read clk (()::tail) rev lefts →
    resident+(encodedLeafInputs clk rows+liveAddRegisters F.hp read tail rev lefts)≤cutRoom) ∧
  (∀ (pre post : List Cmd) (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page)
    (d : ℕ) (wires : List WireRead) (rev : List Bool) (lefts : List (Block F ell)),
    rows=pre++(.packet id pg d wires)::post →
    ClockCut F.hp read clk [] rev lefts →
    SamePacketRegionCuts hf F pos B clk rows pre post id pg d wires rev lefts resident roof ∧
      PacketRetentionCut hf F pos B clk rows pre post id pg d wires rev lefts resident roof)

theorem actual_paid_clock_has_all_its_selected_stop_cuts
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : L)
    (clk : List Unit) (rows : List Cmd) (resident roof : ℕ)
    (fits : resident≤roof) (formats : ∀ row∈rows,ReadFormat B clk.length row) :
    SelectedStopClockCuts hf F pos B clk rows resident roof := by
  let read := actualRowQuery hf F pos B rows
  refine ⟨formats,?_,?_,?_,?_⟩
  · intro pre post cmd rev lefts order cut
    exact Nat.add_le_add fits (measured_read_phase_uses_actual_clock_and_entry
      hf F pos B clk rows pre post cmd order formats rev lefts cut).2.2
  · intro rev lefts cut j
    exact Nat.add_le_add fits (measured_reverse_phase_retains_only_these_named_views hf F pos B clk
      rows rev lefts cut j)
  · intro tail rev lefts cut
    exact Nat.add_le_add fits (measured_add_phase_has_one_actual_pair_and_result hf F pos B clk
      tail rows rev lefts cut)
  · intro pre post id pg d wires rev lefts order cut
    have seen := actual_formatted_packet_keeps_setup_dfs_resize_with_one_regional_roof
      hf F pos B clk rows pre post id pg d wires order formats rev lefts cut resident roof fits
    exact ⟨seen,same_packet_phase_allows_conservative_route_and_table_retention
      hf F pos B clk rows pre post id pg d wires rev lefts resident roof seen⟩

#print axioms actual_paid_clock_has_all_its_selected_stop_cuts
end
end J6R75RawPeak
