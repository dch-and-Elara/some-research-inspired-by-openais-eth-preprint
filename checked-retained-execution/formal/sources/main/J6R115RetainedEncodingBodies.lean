import J6R115RetainedEncodingGate
import J6R114RetainedTerminalTariffBase
import J6R52PeakCache
import J6R51PeakOnlineBodies

/-! Read the exact body words from the original typed lanes and the
real captured frame tape, including the one new lane bit at this read. -/
namespace J6R115RetainedEncoding
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
open J6R52CacheWhole J6R51ParentFrames J6R82LayoutDebit J6R82LeafTime
open J6R9Recursive J6R58LeafScale J6R16ModeCost J6R14LayoutCost J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R10Repack J6R94HeldOwnerProvider J6R110ScopeWordRates
open J6R30ProducedGateRegistry J6R66Active J6R64Active J6R68.RecursivePeak J6R54PeakInput J6R59Public
open J6R51ParentFrames J6R65LeafRate J6R82LeafTime J6R24MeteredRecursion
open J6R111KeptOwnerFlow J6R58BootScope J6R68CanonicalRootWriter J6R51Peak
open J6R114RetainedTerminalTariff J6R48RawRoute J6R52Peak J6R52CacheSource J6R33PageIndexedBirth
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 28000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)


variable (gate : Stamp key prec)

theorem actual_initial_payload_fits_the_original_two_lane_width
    (h : Port (exteriorChild G ell X.centre X.sample X.group).host.Edge) :
    ((initialPayload X gate pad h).2).length≤rootBodyWidth m := by
  let lanes := actualLane X gate pad (edge h).val
  let F := physicalSeatField (rootChart P) (oddAxis m) (residentPageKey m) (edge (edge h).val)
  have l : lanes.gate.body.length=rootHalfWidth m := by
    change (false::(F.page.bits++F.slot.bits)).length=_
    simp only [List.length_cons,List.length_append,F.page.size,F.slot.size,rootHalfWidth]
    omega
  have r : lanes.packet.body.length=2+J6Mesh.a m := by
    change (true::side (edge h).val::F.slot.bits).length=_
    simp only [List.length_cons,F.slot.size]
    omega
  change (if side h then lanes.packet else lanes.gate).body.length≤_
  cases side h
  · simp only [Bool.false_eq_true,if_false,l,rootBodyWidth]
    exact Nat.le_max_left _ _
  · simp only [if_true,r,rootBodyWidth]
    exact Nat.le_max_right _ _

variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (boot : ExactPrintedBoot X M gate)

include boot in
theorem actual_retained_birth_body_has_the_printed_size_roof (h : Port c.host.Edge) :
    ((sourceState M p w).birth.native.physical.record h).body.length≤sourceBodyCap s C (rootBodyWidth m) := by
  have first (slot : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
      (port : Port (exteriorChild G ell X.centre X.sample X.group).host.Edge) :
      ((M.initial slot).result.birth.native.physical.record port).body.length≤rootBodyWidth m := by
    rw [boot.bodies]
    exact actual_initial_payload_fits_the_original_two_lane_width X gate port
  exact actual_demanded_body_fits M (rootBodyWidth m) first p w h

variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (A : CapturedEntry X p w Y)

theorem real_captured_frame_body_bound_from_its_native_words (U : ℕ)
    (raw : ∀ h : Port c.host.Edge,(Y.birth.native.physical.record h).body.length≤U)
    (right : dim (p.ticket w)+2≤U+1) :
    observedFrameWidth (mountResident Y A.resident).result.rows≤U+1 := by
  let mounted := (mountResident Y A.resident).result
  change observedFrameWidth mounted.rows≤_
  rw [observedFrameWidth,(actual_cached_rows_are_the_physical_child mounted).1]
  apply observed_max_bound_of_real_rows
  intro row occurs
  obtain ⟨h,_,rfl⟩ := List.mem_map.mp occurs
  apply max_le
  · change (false::(Y.birth.native.physical.record h.val).body).length≤U+1
    exact Nat.succ_le_succ (raw h.val)
  · change (true::(Y.site.aux h.val).parentWasCol::(Y.site.aux h.val).parentSlot.bits).length≤U+1
    simp only [List.length_cons,(Y.site.aux h.val).parentSlot.size]
    omega

include boot in
theorem real_captured_saved_width_from_exact_boot_and_live_source
    (same : Y=sourceState M p w) :
    observedFrameWidth (mountResident Y A.resident).result.rows≤sourceBodyCap s C (rootBodyWidth m)+1 := by
  have right : dim (p.ticket w)+2≤sourceBodyCap s C (rootBodyWidth m)+1 := by
    have b : dim (p.ticket w)≤Nat.clog 2 s := bits_le_lam (Nat.clog 2 s) c.depth
    have h := Nat.le_max_right (rootBodyWidth m) (Nat.clog 2 s+2)
    unfold sourceBodyCap
    omega
  refine real_captured_frame_body_bound_from_its_native_words X p w Y A _ ?_ right
  intro h
  rw [same]
  exact actual_retained_birth_body_has_the_printed_size_roof X p w gate M boot h

include boot in
theorem exact_positive_retained_input_has_original_saved_and_gate_widths
    (A₀ : CapturedEntry X p w (sourceState M p w)) (d : ℕ) (deg : ∀ v,P.degree v≤d) :
    let input := measuredInputFromCapture X p w M A₀
    observedFrameWidth input.result.saved.rows≤sourceBodyCap s C (rootBodyWidth m)+1 ∧
      observedGateWidth input.result.roster.raw≤max d 2 :=
  ⟨real_captured_saved_width_from_exact_boot_and_live_source X p w gate M boot _ A₀ rfl,
    actual_captured_owner_codes_fit_source_arity X p w _ A₀ d deg⟩

#print axioms actual_initial_payload_fits_the_original_two_lane_width
#print axioms actual_retained_birth_body_has_the_printed_size_roof
#print axioms real_captured_frame_body_bound_from_its_native_words
#print axioms real_captured_saved_width_from_exact_boot_and_live_source
#print axioms exact_positive_retained_input_has_original_saved_and_gate_widths
end
end J6R115RetainedEncoding
