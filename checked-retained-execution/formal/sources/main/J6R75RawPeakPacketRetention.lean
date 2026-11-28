import J6R75RawPeakPacketRegions
import J6R68LeafPeakPacketFinalMul

/-! Conservatively allow the routed packet and affine check tables to
survive both the real creation multiply and the receiver resize.
Use the very same live page recovered by the packet ClockCut. No
release, pointer-sharing or heap lifecycle is assumed. -/
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
set_option maxHeartbeats 6200000

noncomputable section
variable {f : ℤ[X]} {ell p key prec tw bw page : ℕ}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Cmd" => (ReadCmd key page)

theorem same_packet_phase_allows_conservative_route_and_table_retention
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : L)
    (clk : List Unit) (rows pre post : List Cmd)
    (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page) (d : ℕ) (wires : List WireRead)
    (rev : List Bool) (lefts : List (Block F ell)) (resident roof : ℕ)
    (seen : SamePacketRegionCuts hf F pos B clk rows pre post id pg d wires rev lefts resident roof) :
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
        kept+stored+((leafPayload a).length+(leafPayload b).length+scratch+(leafPayload result).length)≤room) := by
  obtain ⟨Q,_,same,_,_,_,resize⟩ := seen
  let bits := (reverseTape rev []).result
  let kept := resident+(encodedLeafInputs clk rows+pendingLeafWords hf F pos B pre rev lefts)
  let common := roof+selectedTerminalRoom (ell:=ell) F clk rows+
    max (Q.routeRoom wires+Q.tableRoom+Q.choiceRoom) (Q.W+ell*(F.words.length*p))
  let A := Q.routeRoom wires+Q.tableRoom
  let stored := Q.routeBits d wires bits+Q.tableSize pos d wires bits
  have storeFit : stored≤A := Nat.add_le_add (Q.exact_routing_fits_generated_page d wires bits).2.2
    (Q.exact_affine_and_test_tables_for_this_page pos d wires bits).2.2.le
  have keepFit : kept≤common :=
    (Nat.le_add_right _ _).trans (resize 0)
  refine ⟨Q,same,?_,?_⟩
  · intro j
    let extra := (leafPayload (Q.createdValue pos d wires bits).result).length+
      ((leafPayload (Q.delivered hf F pos d wires bits).result).take j).length
    change kept+stored+extra≤common+A+13*Q.W
    rw [Nat.add_right_comm]
    exact (Nat.add_le_add (resize j) storeFit).trans (Nat.le_add_right _ _)
  · intro preU head tail cut
    obtain ⟨value,fit⟩ :=
      Q.actual_created_packet_final_multiply_arrays pos d wires bits preU head tail cut
    exact ⟨value,Nat.add_le_add (Nat.add_le_add keepFit storeFit) fit⟩

#print axioms same_packet_phase_allows_conservative_route_and_table_retention
end
end J6R75RawPeak
