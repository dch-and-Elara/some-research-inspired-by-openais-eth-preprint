import J6R75RawPeakStopCore
import J6R68LeafPeakPacketEndpoint

/-! All three named regions of one actual packet at one formatted
ClockCut. Their common upper allowance is the maximum, not a claim
that the regions' temporary storage is simultaneously allocated. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R12
open J6R18ChildWrite J6R19Retained J6R20Ancestor J6R21Ancestor J6R21Leaf
open J6R22Active J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R33StatefulArithmeticPage J6R48Leaf J6R50Leaf J6R62Leaf
open J6R68.LeafPeak J6R68.LeafPeak.Packet

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4350
set_option maxHeartbeats 5900000

noncomputable section
variable {f : ℤ[X]} {ell p key prec tw bw page : ℕ}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Cmd" => (ReadCmd key page)

def SamePacketRegionCuts
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : L)
    (clk : List Unit) (rows pre post : List Cmd)
    (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page) (d : ℕ) (wires : List WireRead)
    (rev : List Bool) (lefts : List (Block F ell)) (resident roof : ℕ) : Prop :=
  ∃ Q : LivePageHit B id pg,
    let bits := (reverseTape rev []).result
    let kept := resident+(encodedLeafInputs clk rows+pendingLeafWords hf F pos B pre rev lefts)
    let current := (.packet id pg d wires : Cmd).read hf F pos B bits
    let common := roof+selectedTerminalRoom (ell:=ell) F clk rows+
      max (Q.routeRoom wires+Q.tableRoom+Q.choiceRoom) (Q.W+ell*(F.words.length*p))
    bits.length=clk.length ∧ current.result=(Q.delivered hf F pos d wires bits).result ∧
    actualRowQuery hf F pos B rows bits=
      (pre.map (fun u=>u.read hf F pos B bits)).foldr (mulM F.hp)
        (mulM F.hp current (actualRowQuery hf F pos B post bits)) ∧
    (∀ j k,kept+(Q.routeBits d wires bits+
      (tableBits ((Q.board pos d wires bits).result.take j)).length+
      ((Q.tests.result.take k).flatMap checkBits).length)≤common) ∧
    (∀ (rs cs : List (Term Q.S.old ell)) (x : Term Q.S.old ell)
      (tail : List (List (Term Q.S.old ell))) (picked : List (List Bool))
      (prod : UVBlock Q.S.old ell) (waiting : List (UVBlock Q.S.old ell)),
      ChoiceCut Q.S.pPos Q.codeWidth Q.S.w Q.tests.result (Q.board pos d wires bits).result
        (oneM Q.S.pPos Q.S.degreePos pos).result ((rs++x::cs)::tail) picked prod waiting →
      let op := choiceOperation Q.S.pPos Q.codeWidth Q.S.w Q.tests.result tail picked prod
      let earlier := rs.map (fun t=>(op t).result)
      let suffix := sumUV Q.S.pPos op cs
      let next := addM Q.S.pPos (op x) suffix
      let work := (waiting.flatMap leafPayload).length+picked.flatten.length+
        (earlier.flatMap leafPayload).length+(leafPayload prod).length+
        (leafPayload (op x).result).length+(leafPayload suffix.result).length+
        (leafPayload next.result).length
      kept+(Q.routeBits d wires bits+Q.tableSize pos d wires bits+work)≤common) ∧
    (∀ j, kept+((leafPayload (Q.createdValue pos d wires bits).result).length+
      ((leafPayload (Q.delivered hf F pos d wires bits).result).take j).length)≤common)

theorem actual_formatted_packet_keeps_setup_dfs_resize_with_one_regional_roof
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : L)
    (clk : List Unit) (rows pre post : List Cmd)
    (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page) (d : ℕ) (wires : List WireRead)
    (order : rows=pre++(.packet id pg d wires)::post)
    (formats : ∀ row∈rows,ReadFormat B clk.length row)
    (rev : List Bool) (lefts : List (Block F ell))
    (cut : ClockCut F.hp (actualRowQuery hf F pos B rows) clk [] rev lefts)
    (resident roof : ℕ) (fit : resident≤roof) :
    SamePacketRegionCuts hf F pos B clk rows pre post id pg d wires rev lefts resident roof := by
  let room := roof+selectedTerminalRoom (ell:=ell) F clk rows
  have before := measured_read_phase_uses_actual_clock_and_entry hf F pos B
    clk rows pre post (.packet id pg d wires) order formats rev lefts cut
  have narrow : resident+(encodedLeafInputs clk rows+
      liveReadRegisters hf F pos B pre (.packet id pg d wires) rev lefts)≤room :=
    Nat.add_le_add fit before.2.2
  obtain ⟨Q,len,val,row,setup,dfs,resize⟩ := actual_formatted_packet_uses_same_leaf_and_stage_reserve
    hf F pos B clk rows pre post id pg d wires order before.2.1 rev lefts cut resident room narrow
  refine ⟨Q,len,val,row,?_,?_,?_⟩
  · intro j k
    exact (setup j k).trans (Nat.add_le_add_left ((Nat.le_add_right _ _).trans (Nat.le_max_left _ _)) _)
  · intro rs cs x tail picked prod waiting event
    exact (dfs rs cs x tail picked prod waiting event).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  · intro j
    exact (resize j).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)

#print axioms actual_formatted_packet_keeps_setup_dfs_resize_with_one_regional_roof
end
end J6R75RawPeak
