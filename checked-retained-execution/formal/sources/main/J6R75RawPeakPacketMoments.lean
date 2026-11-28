import J6R75RawPeakTerminalClock

/-! Source moment product scratch inside the same actual stopped packet.
The real coefficient and earlier factors survive this recursive fold,
with a conservative reserve for its earlier route/affine table. -/
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
set_option maxHeartbeats 8900000

noncomputable section
variable {f : ℤ[X]} {ell p key prec tw bw page : ℕ}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Cmd" => (ReadCmd key page)

def PacketMomentFoldCut
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : L)
    (clk : List Unit) (rows pre : List Cmd)
    (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page)
    (d : ℕ) (wires : List WireRead) (rev : List Bool) (lefts : List (Block F ell))
    (resident roof : ℕ) : Prop :=
  ∃ Q : LivePageHit B id pg,
    let bits := (reverseTape rev []).result
    let kept := resident+(encodedLeafInputs clk rows+pendingLeafWords hf F pos B pre rev lefts)
    let stored := Q.routeBits d wires bits+Q.tableSize pos d wires bits
    let common := roof+selectedTerminalRoom (ell:=ell) F clk rows+
      max (Q.routeRoom wires+Q.tableRoom+Q.choiceRoom) (Q.W+ell*(F.words.length*p))
    let room := common+(Q.routeRoom wires+Q.tableRoom)+((Q.data.modes.length+3)*Q.W+10*Q.W)
    ((.packet id pg d wires : Cmd).read hf F pos B bits).result=
      (Q.delivered hf F pos d wires bits).result ∧
    ∀ (old new : List (ModeInput Q.S.a Q.S.p Q.S.i Q.S.w)) (k : ModeInput Q.S.a Q.S.p Q.S.i Q.S.w),
      Q.data.modes=old++k::new →
      let cs := (Q.routed d wires bits).result.2
      let op := sourcePower (q:=Q.S.w) Q.S.pPos Q.S.degreePos pos Q.S.i cs
      let prev := old.map op
      let now := op k
      let tail := sourceProduct Q.S.pPos Q.S.degreePos pos Q.S.i cs new
      let partialBits := (leafPayload (Q.coefficient pos d wires bits).result).length+
        ((prev.map Meter.result).flatMap leafPayload).length+
        (leafPayload now.result).length+(leafPayload tail.result).length+
        (leafPayload (mulM Q.S.pPos now tail).result).length
      Q.moments pos d wires bits=prev.foldr (mulM Q.S.pPos) (mulM Q.S.pPos now tail) ∧
      (∀ (before : List (UBlock Q.S.old)) (head : UBlock Q.S.old) (after : List (UBlock Q.S.old)),
        now.result.val=before++head::after →
        let arrays := (encodeArrays scalarPayload
          (combineArrays (uGates Q.S.pPos Q.S.old) head after tail.result.val)).length
        kept+stored+(partialBits+arrays)≤room)

theorem actual_formatted_stop_packet_has_named_moment_fold_and_arrays
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : L)
    (clk : List Unit) (rows pre post : List Cmd)
    (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page) (d : ℕ) (wires : List WireRead)
    (rev : List Bool) (lefts : List (Block F ell)) (resident roof : ℕ)
    (checked : SelectedStopClockCuts hf F pos B clk rows resident roof)
    (order : rows=pre++(.packet id pg d wires)::post)
    (cut : ClockCut F.hp (actualRowQuery hf F pos B rows) clk [] rev lefts) :
    PacketMomentFoldCut hf F pos B clk rows pre id pg d wires rev lefts resident roof := by
  obtain ⟨Q,_,same,_,_,_,resize⟩ := (checked.2.2.2.2 pre post id pg d wires rev lefts order cut).1
  let bits := (reverseTape rev []).result
  let kept := resident+(encodedLeafInputs clk rows+pendingLeafWords hf F pos B pre rev lefts)
  let common := roof+selectedTerminalRoom (ell:=ell) F clk rows+
    max (Q.routeRoom wires+Q.tableRoom+Q.choiceRoom) (Q.W+ell*(F.words.length*p))
  let A := Q.routeRoom wires+Q.tableRoom
  let stored := Q.routeBits d wires bits+Q.tableSize pos d wires bits
  have storeFit : stored≤A := Nat.add_le_add
    (Q.exact_routing_fits_generated_page d wires bits).2.2
    (Q.exact_affine_and_test_tables_for_this_page pos d wires bits).2.2.le
  have keepFit : kept≤common := (Nat.le_add_right _ _).trans (resize 0)
  refine ⟨Q,same,?_⟩
  intro old new k orderModes
  obtain ⟨ran,modeFit⟩ := Q.true_entry_source_mode_cut pos d wires bits old new k orderModes
  refine ⟨ran,?_⟩
  intro before head after site
  let cs := (Q.routed d wires bits).result.2
  let op := sourcePower (q:=Q.S.w) Q.S.pPos Q.S.degreePos pos Q.S.i cs
  let now := op k
  let tail := sourceProduct Q.S.pPos Q.S.degreePos pos Q.S.i cs new
  have arrays := native_v_convolution_scratch Q.S.pPos now.result tail.result before head after site
  have arFit :
      (encodeArrays scalarPayload (combineArrays (uGates Q.S.pPos Q.S.old) head after tail.result.val)).length
        ≤10*Q.W := by
    simpa only [LivePageHit.W,Nat.mul_assoc] using arrays
  exact Nat.add_le_add (Nat.add_le_add keepFit storeFit) (Nat.add_le_add modeFit arFit)

#print axioms actual_formatted_stop_packet_has_named_moment_fold_and_arrays
end
end J6R75RawPeak
