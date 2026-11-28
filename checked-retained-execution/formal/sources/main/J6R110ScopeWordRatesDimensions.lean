import J6R110ScopeWordRatesNumeric
import J6R57ScopeFeeCaps

/-! Real source-word bounds from the lengths of the selected request's
actual input and source tapes. No whole replay or occurrence fee is a
premise; all scans are charged at their original call sites. -/
namespace J6R110ScopeWordRates
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R48RawRoute
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R49SourceLayout J6R50SourceProducer J6R51Online
open J6R52Dispatch J6R53Dispatch J6R54Dispatch J6R55Dispatch J6R55Public J6R54PublicFamily
open J6R57ScopeFee J6R68RateJoint J6R88ScopeCode J6R92NativeWidth J6R102NativeCodeMeter
open J6R10Repack J6R27OriginalGate J6R82LayoutDebit

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14500000
set_option maxRecDepth 4900
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}

local notation "S" => (printedParams (f:=f) (ell:=ell) s)

/-- All guards refer to the actual selected physical tape or source word.
The possibly noncanonical length of `emitted.rows` is not inferred from
edge coverage; if a canonical R59 table is selected its bound is exact. -/
structure LiteralRequestSizes (I : Meter (FixedRequest X w)) (K : ℕ) : Prop where
  keyPos : 0<key
  keyRoom : X.birth.job.identifier.val+1<2^key
  keyWidth : key≤K
  depthWidth : I.result.shell.dep≤K
  precisionWidth : prec≤K
  timeWidth : tw≤K
  codeWidth : bw≤K
  lambdaWidth : Nat.clog 2 s≤K
  rank : I.result.q+1≤K
  axisWord : (printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth≤K
  hdrCount : 2^(6*((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth))*
    2^(6*((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth))≤K
  copies : (packing sel (ticketReady T (successorTicket v w))).copies≤K
  tileCount : 2^((centerIndex (ticketReady T (successorTicket v w)) (successorTicket v w).centerAt).val+1)≤K
  receive : registerPrecision (printedParams (f:=f) (ell:=ell) s) v.child (successorTicket v w).centerAt≤K
  ports : X.birth.port≤K
  owner : X.site.ownerWidth≤K
  pageWidth : page≤K
  edges : v.child.edges≤K
  seatRows : I.result.emitted.rows.length≤K
  maskRows : I.result.emitted.masks.length≤K
  maskFields : ∀ x∈I.result.emitted.masks,
    x.address.labels.1.length≤K ∧ x.address.labels.2.length≤K ∧ x.bits.length≤K
  frames : ∀ e∈childOrder X.site,(frameOf X.site e).left.body.length≤K ∧ (frameOf X.site e).right.body.length≤K
  labelCode : leastRosterCode I.result.replay.resident.raw.roster.modes.length≤K

variable (I : Meter (FixedRequest X w)) {K : ℕ} (H : LiteralRequestSizes I K)

private theorem frame_count_from_actual_child_order : (childOrder X.site).length=v.child.edges := by
  simp [childOrder]

include H in
theorem actual_next_half_word_writer_has_physical_roof :
    nextPortWordsTariff (X:=X) I.result.q≤6+K*(59*K+70) := by
  let A := (printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth
  let E := childOrder X.site
  let q := I.result.q
  let one := fun e=>framedCopiesFee (frameOf X.site e)+3*A+3*((q-A)+13*A)+8
  have len : E.length≤K := (frame_count_from_actual_child_order (X:=X)).trans_le H.edges
  have sum := sum_mapped_bounded E one (59*K+70) (by
    intro e here
    obtain ⟨l,r0⟩ := H.frames e here
    have c := side_port_writer_is_bounded_by_actual_body_words (frameOf X.site e) H.ports l r0
    have p : q+1≤K := H.rank
    have a : A≤K := H.axisWord
    change framedCopiesFee (frameOf X.site e)+3*A+3*((q-A)+13*A)+8≤_
    omega)
  change 6+(E.map one).sum≤_
  exact Nat.add_le_add_left (sum.trans (Nat.mul_le_mul_left _ len)) _ |>.trans_eq (by rw [Nat.mul_comm (59*K+70) K])

include H in
theorem actual_selected_replay_has_physical_roof :
    selectedResidentWordsTariff (X:=X) (w:=w) I.result.emitted≤
      (3+K*(36*K+66))+(4+K*(locateFee K K+45*K+54))+replayGeometryRoof K+7 := by
  let A := (printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth
  let E := childOrder X.site
  let q := I.result.q
  let rows := I.result.emitted.rows
  let masks := I.result.emitted.masks
  let frames := E.map (frameOf X.site)
  have len : E.length≤K := (frame_count_from_actual_child_order (X:=X)).trans_le H.edges
  have fl : frames.length≤K := by simpa only [frames,List.length_map] using len
  have F := sum_mapped_bounded frames (fun x=>3*X.birth.port+5+framedIncidenceFee x) (36*K+66) (by
    intro x mem
    obtain ⟨e,h,rfl⟩ := List.mem_map.mp mem
    obtain ⟨l,r0⟩ := H.frames e h
    have pp := incidence_row_width_cap (frameOf X.site e) H.ports H.owner H.keyWidth H.precisionWidth H.pageWidth l r0
    have p := H.ports
    change 3*X.birth.port+5+framedIncidenceFee (frameOf X.site e)≤_
    omega)
  have F' : (frames.map (fun x=>3*X.birth.port+5+framedIncidenceFee x)).sum≤K*(36*K+66) := by
    exact (F.trans (Nat.mul_le_mul_left _ fl)).trans_eq (Nat.mul_comm _ _)
  have Q : locateFee X.birth.port rows.length+3*(A+((q-A)+13*A))+54 ≤ locateFee K K+45*K+54 := by
    have rr : q+1≤K := H.rank
    have a : A≤K := H.axisWord
    have loc := locate_fee_mono_width_tables H.ports H.seatRows
    change locateFee X.birth.port rows.length≤_ at loc
    omega
  have M0 := sum_mapped_bounded masks (fun x=>copiedMaskFee x+5) (12*K+18) (by
    intro x mem
    obtain ⟨l,r0,bits⟩ := H.maskFields x mem
    exact real_mask_row_copy_fits_width x H.rank l r0 bits)
  have mask : (masks.map (fun x=>copiedMaskFee x+5)).sum≤K*(12*K+18) := by
    exact (M0.trans (Nat.mul_le_mul_left _ H.maskRows)).trans_eq (Nat.mul_comm _ _)
  have G := real_replay_from_physical_extents H.axisWord H.rank H.hdrCount H.copies H.tileCount H.receive mask len
  unfold selectedResidentWordsTariff
  change (3+(frames.map (fun x=>3*X.birth.port+5+framedIncidenceFee x)).sum)+
      (4+E.length*(locateFee X.birth.port rows.length+3*(A+((q-A)+13*A))+54))+
      selectedReplayFee A q (centerIndex (ticketReady T (successorTicket v w)) (successorTicket v w).centerAt).val
        (packing sel (ticketReady T (successorTicket v w))).copies
        (registerPrecision S v.child (successorTicket v w).centerAt)
        ((masks.map (fun x=>copiedMaskFee x+5)).sum) E.length+7≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left F' 3)
    (Nat.add_le_add_left (Nat.mul_le_mul len Q) 4)) G) 7

include H in
theorem selected_R102_descendant_words_are_bounded_by_literal_dimensions :
    measuredWordProducers (measureLocalLoad (meteredSelectedDemand I).result).result.advance.next.input≤
      descendantSourceWordsRoof K := by
  have actual := R102_selected_source_words_include_new_code_and_keep_shell_prices I K H.keyPos H.keyRoom
    H.keyWidth H.depthWidth H.precisionWidth H.timeWidth H.codeWidth H.lambdaWidth
  have ports := actual_next_half_word_writer_has_physical_roof I H
  have replay := actual_selected_replay_has_physical_roof I H
  have ord : ordinalFee bw (leastRosterCode I.result.replay.resident.raw.roster.modes.length)≤ordinalFee K K := by
    unfold ordinalFee
    have f1 := Nat.mul_le_mul_left 4 H.codeWidth
    have f2 : 13*bw+7≤13*K+7 := Nat.add_le_add_right (Nat.mul_le_mul_left 13 H.codeWidth) 7
    exact Nat.add_le_add (Nat.add_le_add_right f1 4) (Nat.mul_le_mul H.labelCode f2)
  dsimp only at actual
  refine actual.trans ?_
  unfold descendantSourceWordsRoof
  have roof := Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add ports replay) (40*K+45)) ord) 3
  convert roof using 1; ring

end
#print axioms actual_next_half_word_writer_has_physical_roof
#print axioms actual_selected_replay_has_physical_roof
#print axioms selected_R102_descendant_words_are_bounded_by_literal_dimensions
end J6R110ScopeWordRates