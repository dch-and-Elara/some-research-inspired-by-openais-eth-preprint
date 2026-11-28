import J6R58LeafScalePage
import J6R58LeafScalePrecision
import J6R34RootAtlasOccurrence

/-! These are the precise chart and proof used by compileOccurrence
itself. Geometry is carried across the actual public page-width cast. -/
namespace J6R58LeafScale
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R17ModeTape
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R10Repack J6R24MeteredRecursion J6R26DescriptorTree J6R16ModeCost
open J6R33GeneratedChildSite J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R34RootAtlas J6R48DFS
open J6R32ChildResidentTransfer P11FullPacking J6R50Peak J6R18ChildWrite J6R57LeafCap
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 4200
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)

noncomputable def chosenAtlas (I : OccurrenceInput T v key prec tw bw page) :=
  Classical.choice (occurrence_real_receipt I)

private theorem cast_keeps_actual_rows_length {a b : ℕ} (e : a=b)
    (R : J6R33StatefulArithmeticPage.Birth T v key prec tw bw a) :
    ((e ▸ R : J6R33StatefulArithmeticPage.Birth T v key prec tw bw b)).rows.length=R.rows.length := by
  cases e
  rfl

theorem compiled_occurrence_rows_are_selected_atlas_count
    (I : OccurrenceInput T v key prec tw bw page) :
    (compileOccurrence I).rows.length=
      Nat.card (Page ((SP).levelBits v.parent.depth)
        (packing sel (ticketReady T v)).copies (Fin 64)) := by
  let axis := (SP).levelBits v.parent.depth
  let copies := (packing sel (ticketReady T v)).copies
  let A := chosenAtlas I
  let paid := padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)
  let birth := issuedBirth I.native.result paid I.words.result I.hOld A
  have eq := cast_keeps_actual_rows_length I.width birth
  change (compileOccurrence I).rows.length=A.bank.length at eq
  rw [eq,A.order,List.length_map]
  obtain ⟨nd,all,_⟩ := child_pages_complete axis copies
  exact (Nat.card_fin _).symm.trans (Nat.card_congr
    (nd.getEquivOfForallMemList (orderedChildPages axis copies) all))

theorem actual_occurrence_compact_chart (par : Path sel r c) (w : (Plan sel).Slot c)
    (I : OccurrenceInput T (par.ticket w) key prec tw bw page) :
    let v := par.ticket w
    let a := (SP).levelBits c.depth
    let p := registerPrecision SP c v.centerAt
    let A := chosenAtlas I
    (compileOccurrence I).rows.length*2^a≤3*(C*s) ∧
      p≤r.prec+160*C*s^2 ∧
      ∀ k, (A.page k).fields.rows.length≤2^a ∧ (A.page k).fields.cols.length≤2^a ∧
        (A.page k).fields.modes.length≤3*(C*s)*p := by
  let v := par.ticket w
  let P := packing sel (ticketReady T v)
  let a := (SP).levelBits c.depth
  let p := registerPrecision SP c v.centerAt
  let F := chosenAtlas I
  have edges : Nat.card c.host.Edge=c.edges := by
    letI := c.host.finiteEdge
    rw [Nat.card_eq_fintype_card]
    exact (ticketReady T v).edgeCount
  have cover : c.edges≤C*s := actual_source_path_edges_le (cfg:=cfg) sel T.rootStable par
  have total : 3*Nat.card c.host.Edge≤3*(C*s) :=
    Nat.mul_le_mul_left _ (edges.trans_le cover)
  have area : (compileOccurrence I).rows.length*2^a≤3*(C*s) := by
    rw [compiled_occurrence_rows_are_selected_atlas_count I]
    exact (true_padded_atlas_area (P:=P)).trans total
  refine ⟨area,actual_native_register_quadratic (cfg:=cfg) sel T.rootStable par w.property v.centerAt,?_⟩
  intro k
  have dims := actual_published_page_dimensions I.geometry (F.page k)
  exact ⟨dims.1,dims.2.1,dims.2.2.trans (Nat.mul_le_mul_right p total)⟩

theorem actual_occurrence_packet_geometric_not_promised
    (par : Path sel r c) (w : (Plan sel).Slot c)
    (I : OccurrenceInput T (par.ticket w) key prec tw bw page) (rootPrec : r.prec≤C*s) :
    let v := par.ticket w
    let a := (SP).levelBits c.depth
    let p := registerPrecision SP c v.centerAt
    let i := (centerIndex (ticketReady T v) v.centerAt).val
    let A := chosenAtlas I
    let hp := register_positive (ticketReady T v) v.centerAt
    let H := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
    ∀ k,
      let fld := (A.page k).fields
      let e := I.fw.length
      let l := fld.rows.length
      let j := fld.cols.length
      let m := fld.modes.length
      packetFee a e ell p i (I.q+1) I.code l j m hp+packetFramingFee e ell p (I.q+1)≤
        2^(6*H)*(packetNonTreeFee a e ell p i (I.q+1) I.code l j m hp+
          packetTreeScale e ell p m l I.code (I.q+1) hp+packetFramingFee e ell p (I.q+1)) := by
  intro v a p i F hp H k fld e l j m
  have dim := actual_occurrence_compact_chart par w I
  have hm : m+2≤2^(6*Nat.clog 2 s) :=
    source_register_bound s C m p r.prec (root_lambda_large cfg) cfg.constSmall rootPrec
      dim.2.1 (dim.2.2 k).2.2
  exact actual_printed_packet_entry_geometric s c.depth e ell p i (I.q+1) I.code l j m 6 hp
    (root_lambda_large cfg) (dim.2.2 k).1 hm

#print axioms compiled_occurrence_rows_are_selected_atlas_count
#print axioms actual_occurrence_compact_chart
#print axioms actual_occurrence_packet_geometric_not_promised
end
end J6R58LeafScale
