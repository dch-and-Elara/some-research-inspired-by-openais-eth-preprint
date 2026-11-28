import J6R57ScopeFeeAtlasGeometry
import J6R58LeafScaleNative
import J6R51OnlineCore

/-! The actual compiler atlas of a reached occurrence has a polynomial
footprint. The copies and the mode roster are genuine counts supplied by
the selected layout and its complete physical receipt, not promises. -/
namespace J6R85ScopeProducer
open scoped Polynomial Classical
open Polynomial J6R16ModeCost J6R15ModeCost J6R32StatefulArithmetic
open J6R24MeteredRecursion J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R26DescriptorTree J6R34RootAtlas J6R33GeneratedChildSite J6R33PageIndexedBirth J6R32ChildResidentTransfer
open J6R58LeafScale J6R57ScopeFee J6R30ProducedGateRegistry P11FullPacking J6R51Online

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 3900
set_option maxHeartbeats 18000000

/-- No callback costs, directory lengths, or proven mesh fields are
inputs to this roof. Code is the actual numeric code-size field. -/
def atlasSourceRoof (s C p0 ell page tw bw code : ℕ) : ℕ :=
  (2*s)^6+(page+1)+3*(C*s)+(p0+160*C*s^2)+
    (ell+4*Nat.clog 2 s+code)+3*(C*s)*(p0+160*C*s^2)+tw+bw

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Plan₀" => (@Plan f ell s sel)

theorem actual_atlas_footprint_from_printed_source
    (p : Path sel r c) (w : (Plan₀).Slot c)
    (I : OccurrenceInput T (p.ticket w) key prec tw bw page)
    (code : ℕ) (codeWidth : I.code≤code) :
    AtlasFootprint I (atlasSourceRoof s C r.prec ell page tw bw code) := by
  let v := p.ticket w
  let d := ticketReady T v
  let shape := packing sel d
  let a := (SP).levelBits c.depth
  let timePrec := registerPrecision SP c v.centerAt
  let roof := atlasSourceRoof s C r.prec ell page tw bw code
  have hDim : a≤Nat.clog 2 s := bits_le_lam _ _
  have hn : 1<s := (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).1
    (show 0<Nat.clog 2 s from (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg))
  have hCells : (2:ℕ)^(6*a)≤(2*s)^6 :=
    printed_literal_header_side_is_polynomial (f:=f) (ell:=ell) c.depth hn
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have card : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact d.edgeCount
  have es : c.edges≤C*s := actual_source_path_edges_le (cfg:=cfg) sel T.rootStable p
  have realEdges : I.geometry.edges.length≤C*s := by
    letI : Fintype (p.ticket w).parent.host.Edge := (p.ticket w).parent.host.finiteEdge
    have h := full_roster_length I.geometry.edges I.geometry.edgesUnique I.geometry.edgesAll
    change I.geometry.edges.length=Nat.card c.host.Edge at h
    rw [h,card]
    exact es
  have capPrec : timePrec≤r.prec+160*C*s^2 :=
    actual_native_register_quadratic (cfg:=cfg) sel T.rootStable p w.property v.centerAt
  have realModes : I.geometry.modes.length≤3*(C*s)*(r.prec+160*C*s^2) := by
    have h := actual_mode_roster_fits_padded_area I.geometry
    change I.geometry.modes.length≤3*Nat.card c.host.Edge*timePrec at h
    rw [card] at h
    exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ es) capPrec)
  have padded : Nat.card (Page a shape.copies (Fin 64))*2^a≤3*(C*s) := by
    have h := true_padded_atlas_area (P:=shape)
    change Nat.card (Page a shape.copies (Fin 64))*2^a≤3*Nat.card c.host.Edge at h
    rw [card] at h
    exact h.trans (Nat.mul_le_mul_left _ es)
  have census : Nat.card (Page a shape.copies (Fin 64))=pagesCount a shape.copies := by
    obtain ⟨nd,all,lens⟩ := child_pages_complete a shape.copies
    exact (full_roster_length _ nd all).symm.trans lens
  have realCopies : shape.copies≤3*(C*s) := by
    have small : shape.copies≤pagesCount a shape.copies := by
      unfold pagesCount
      exact Nat.le_mul_of_pos_left _ (by positivity)
    have h := (Nat.le_mul_of_pos_right (Nat.card (Page a shape.copies (Fin 64))) (by positivity : 0<(2:ℕ)^a)).trans padded
    rw [census] at h
    exact small.trans h
  have rosterWidth : I.q+1≤page+1 := by
    have h := I.width
    omega
  let F : Frame f timePrec := ⟨register_positive d v.centerAt,I.fw,I.hOld,I.hMod⟩
  have degree : I.fw.length=4*Nat.clog 2 s :=
    (F.natDegree hf).trans cfg.coefficient
  change AtlasFootprint I roof
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a≤roof
    unfold roof atlasSourceRoof
    omega
  · change 2^(6*a)≤roof
    unfold roof atlasSourceRoof
    omega
  · unfold roof atlasSourceRoof
    omega
  · change shape.copies≤roof
    unfold roof atlasSourceRoof
    omega
  · change timePrec≤roof
    unfold roof atlasSourceRoof
    omega
  all_goals (unfold roof atlasSourceRoof; omega)

theorem same_online_occurrences_have_printed_atlas
    (M : OnlineMachine T key prec tw bw page q) (code : ℕ)
    (size : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan₀).Slot x),
      (sourceState M p w).input.code≤code)
    (p : Path sel r c) (w : (Plan₀).Slot c) :
    AtlasFootprint (sourceState M p w).input (atlasSourceRoof s C r.prec ell page tw bw code) :=
  actual_atlas_footprint_from_printed_source p w (sourceState M p w).input code (size p w)

/-- A fully explicit finite bound even for the legacy arbitrary encoded
context. A polynomial-time application must bound the numeric field;
arbitrary padding of the encoding is not assumed inexpensive. -/
theorem same_online_occurrence_atlas_from_raw_code_storage
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) (w : (Plan₀).Slot c) :
    AtlasFootprint (sourceState M p w).input (atlasSourceRoof s C r.prec ell page tw bw (2^bw)) := by
  let I := (sourceState M p w).input
  have fit : I.code≤2^bw := by
    rw [← I.codeExact]
    exact (val_lt I.words.result.context.codeWidth).le
  exact actual_atlas_footprint_from_printed_source p w I (2^bw) fit

#print axioms actual_atlas_footprint_from_printed_source
#print axioms same_online_occurrences_have_printed_atlas
#print axioms same_online_occurrence_atlas_from_raw_code_storage
end
end J6R85ScopeProducer
