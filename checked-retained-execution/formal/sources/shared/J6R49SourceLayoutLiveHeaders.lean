import J6R49SourceLayoutOwners

/-! The next target tape can now be assembled from the live parent
header roster and its actual all-page birth. No separately provided
list of next rows, pages, incidences, seats, masks or mode roster is
used in this metered one-site preparation. -/
namespace J6R49SourceLayout
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate J6R34RootAtlas
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes J6R32ChildResidentTransfer
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10400000
set_option maxRecDepth 3050
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {I : OccurrenceInput T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs (compileOccurrence I) previous)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
local instance LiveChildFinite : Fintype v.child.host.Edge := v.child.host.finiteEdge
local instance LiveRowFinite : Fintype v.child.host.Row := v.child.host.finiteRow
local instance LiveColFinite : Fintype v.child.host.Col := v.child.host.finiteCol

def liveVertexKeys (parents : ParentOwnerHeaders S) (canonical : S.pageKey=occurrencePageWord I) :
    Meter (VertexKeys S) :=
  let rows := readOldVertices S parents
  let cols := vertexKeysOfBirth S rows.result canonical
  ⟨cols.result,rows.steps+cols.steps+4⟩

theorem live_vertex_keys_exact (parents : ParentOwnerHeaders S) (canonical : S.pageKey=occurrencePageWord I) :
    let W := liveVertexKeys S parents canonical
    W.result.rawRows=(selectOwnerKeys (word v.groupAt.val) parents.raw).result ∧
      W.result.rawCols=(readBankKeys (compileOccurrence I).rows).result ∧
      W.steps=(7+(3*S.ownerWidth+77)*parents.raw.length+(3*S.ownerWidth+1)*W.result.rows.length)+
        (7+(3*page+7)*(compileOccurrence I).rows.length)+4 := by
  let O := readOldVertices S parents
  let V := vertexKeysOfBirth S O.result canonical
  have l := exact_old_vertices_from_grouped_headers S parents
  have r := exact_vertex_roster_from_actual_birth S O.result canonical
  refine ⟨r.1.trans l.1,r.2.1,?_⟩
  change O.steps+V.steps+4=(7+(3*S.ownerWidth+77)*parents.raw.length+
    (3*S.ownerWidth+1)*O.result.rows.length)+(7+(3*page+7)*(compileOccurrence I).rows.length)+4
  rw [show O.steps=_ from l.2,show V.steps=_ from r.2.2.2]

def prepareFromLiveHeaders (parents : ParentOwnerHeaders S) (canonical : S.pageKey=occurrencePageWord I)
    (q i : ℕ) (axis : List Bool) (pr : Word (q+1)) : Meter (Option (PreparedSeats A q)) :=
  let U := liveVertexKeys S parents canonical
  let W := prepareDescendant S q i axis U.result.rawRows U.result.rawCols pr
  ⟨W.result,U.steps+W.steps+5⟩

theorem live_parent_frames_and_headers_prepare_actual_site
    (parents : ParentOwnerHeaders S) (canonical : S.pageKey=occurrencePageWord I)
    (oldInjective : Function.Injective S.oldKey)
    (d : Ready SP (sourceDelta s) v.child) (t : Center SP v.child)
    {q : ℕ} (hq : 0<q) (ha : A≤q) (fit : v.child.edges<2^q)
    (axis : List Bool) (clock : axis.length=(centerIndex d t).val)
    (precision : Word (q+1)) (readPrecision : precision.val=registerPrecision SP v.child t) :
    let U := liveVertexKeys S parents canonical
    let F := nativeFormat (a:=A) S fit oldInjective
      (canonical.symm ▸ occurrence_page_word_injective I : Function.Injective S.pageKey)
    let out := prepareFromLiveHeaders S parents canonical q (centerIndex d t).val axis precision
    ∃ X : GeneratedChild S d t out,
      out.steps≤U.steps+
        (orderedIncidenceFee S+((6*S.ownerWidth+22)*U.result.rows.length+
          (3*page+13)*U.result.cols.length+4)+
          preparedSeatFee F q (centerIndex d t).val X.chart.copies (registerPrecision SP v.child t)
            X.data.native.raw.packed.boxes+6)+5 := by
  let U := liveVertexKeys S parents canonical
  have ci : Function.Injective S.pageKey := canonical.symm ▸ occurrence_page_word_injective I
  obtain ⟨B,bill⟩ := actual_frames_generate_descendant S d t hq ha fit oldInjective ci
    U.result axis clock precision readPrecision
  refine ⟨⟨B.chart,B.data,B.success,B.mask,B.receipt,B.ordered⟩,?_⟩
  exact Nat.add_le_add_right (Nat.add_le_add_left bill U.steps) 5

#print axioms live_vertex_keys_exact
#print axioms live_parent_frames_and_headers_prepare_actual_site
end
end J6R49SourceLayout