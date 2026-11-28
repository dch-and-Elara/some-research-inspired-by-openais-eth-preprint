import J6R49SourceLayoutFrames
import J6R49SourceLayoutGeneration

/-! One actual next active site: paid incidence from the predecessor,
complete registered vertex-key tables, and the printed receiving
precision. The same stable greedy output supplies resident masks,
seats and modes, and its separate native-order tape. -/
namespace J6R49SourceLayout
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes J6R11Repack
open J6R32ChildResidentTransfer J6R48RawRoute J6R12CollisionGreedyStep J6R12CollisionMenu
open J6R33GeneratedChildSite J6R14LayoutCost
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2900
set_option maxHeartbeats 10500000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs Q previous)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
local notation "E" => v.child.host.Edge
local notation "R" => v.child.host.Row
local notation "D" => v.child.host.Col
local instance finiteActualDescendant : Fintype E := v.child.host.finiteEdge
local instance finiteActualRow : Fintype R := v.child.host.finiteRow
local instance finiteActualCol : Fintype D := v.child.host.finiteCol

structure VertexKeys (S : SiteInputs Q previous) where
  rows : List R
  cols : List D
  rowsUnique : rows.Nodup
  colsUnique : cols.Nodup
  rowsAll : ∀ u,u∈rows
  colsAll : ∀ u,u∈cols
  rawRows : List (Word S.ownerWidth)
  rawCols : List (Word page)
  exactRows : rawRows=rows.map (nativeRowKey S)
  exactCols : rawCols=cols.map (nativeColKey S)

def VertexKeys.order (U : VertexKeys S) : List (R⊕D) :=
  U.rows.map Sum.inl++U.cols.map Sum.inr

theorem VertexKeys.valid_order (U : VertexKeys S) :
    (U.order S).Nodup ∧ ∀ z,z∈U.order S := by
  constructor
  · apply List.Nodup.append
    · exact U.rowsUnique.map Sum.inl_injective
    · exact U.colsUnique.map Sum.inr_injective
    · intro x hx hy
      obtain ⟨old,_,rfl⟩ := List.mem_map.mp hx
      obtain ⟨pg,_,bad⟩ := List.mem_map.mp hy
      cases bad
  · intro z
    cases z with
    | inl x => exact List.mem_append_left _ (List.mem_map.mpr ⟨x,U.rowsAll x,rfl⟩)
    | inr y => exact List.mem_append_right _ (List.mem_map.mpr ⟨y,U.colsAll y,rfl⟩)

theorem targets_from_registered_keys {q : ℕ} (fit : v.child.edges<2^q)
    (rowKey : Function.Injective S.oldKey) (colKey : Function.Injective S.pageKey)
    (U : VertexKeys S) :
    let F := nativeFormat (a:=A) S fit rowKey colKey
    let W := writeTargets U.rawRows U.rawCols
    W.result=(U.order S).map F.target ∧
      W.steps≤(6*S.ownerWidth+22)*U.rows.length+(3*page+13)*U.cols.length+4 := by
  let old := nativeRowKey S
  let pg := nativeColKey S
  let rowInj : Function.Injective old :=
    rowKey.comp (Subtype.val_injective.comp (physicalChildRows (T:=T) (v:=v)).injective)
  let colInj : Function.Injective pg :=
    colKey.comp (physicalChildCols (T:=T) (v:=v)).injective
  dsimp only
  rw [U.exactRows,U.exactCols]
  exact typed_target_tape (a:=A) v.child.host.network q
    ((actual_child_card (Q:=Q)).trans_lt fit) (childOrder S) (child_order_complete S).1
    (child_order_complete S).2 old pg rowInj colInj U.rows U.cols

def prepareDescendant (q i : ℕ) (axis : List Bool)
    (rowKeys : List (Word S.ownerWidth)) (pageKeys : List (Word page))
    (precision : Word (q+1)) : Meter (Option (PreparedSeats A q)) :=
  let W := sourceIncidence S
  match W.result with
  | none=>⟨none,W.steps+3⟩
  | some raw =>
    let G := writeTargets rowKeys pageKeys
    let L := prepareGreedySeats A q S.ownerWidth page (6*A) q i axis G.result raw precision
    ⟨L.result,W.steps+G.steps+L.steps+6⟩

def orderedIncidenceFee : ℕ :=
  7+((childOrder S).map (fun e=>framedIncidenceFee (frameOf S e)+6)).sum

structure GeneratedChild (d : Ready SP (sourceDelta s) v.child)
    (t : Center SP v.child) {q : ℕ}
    (out : Meter (Option (PreparedSeats A q))) where
  chart : PhysicalPacking v.child.host.network A (Fin 64)
  data : PreparedSeats A q
  success : out.result=some data
  mask : chart.mask=childMask A chart.copies
  receipt : ResidentReceipt chart (centerIndex d t) (registerPrecision SP v.child t) data.native
  ordered : data.ordered=(childOrder S).map
    (physicalSeatField chart (centerIndex d t) (childPageKey (q-A)))

theorem actual_frames_generate_descendant (d : Ready SP (sourceDelta s) v.child)
    (t : Center SP v.child) {q : ℕ} (hq : 0<q) (ha : A≤q) (fit : v.child.edges<2^q)
    (rowKey : Function.Injective S.oldKey) (colKey : Function.Injective S.pageKey)
    (U : VertexKeys S) (axis : List Bool) (clock : axis.length=(centerIndex d t).val)
    (precision : Word (q+1)) (readPrecision : precision.val=registerPrecision SP v.child t) :
    let F := nativeFormat (a:=A) S fit rowKey colKey
    let out := prepareDescendant S q (centerIndex d t).val axis U.rawRows U.rawCols precision
    ∃ X : GeneratedChild S d t out,
      out.steps≤orderedIncidenceFee S+
        ((6*S.ownerWidth+22)*U.rows.length+(3*page+13)*U.cols.length+4)+
        preparedSeatFee F q (centerIndex d t).val X.chart.copies (registerPrecision SP v.child t)
          X.data.native.raw.packed.boxes+6 := by
  let F := nativeFormat (a:=A) S fit rowKey colKey
  let p := sourceDelta s
  let i := centerIndex d t
  let vs := U.order S
  have N := U.valid_order S
  have hFormat : ∀ x,F.label x=coordinateLabel x := by
    intro x
    unfold F nativeFormat
    exact child_format_label _ _ _ _ _ _ _ _ _ _ x
  have hcard : Fintype.card E<2^q := (actual_child_card (Q:=Q)).trans_lt fit
  have nc : Nat.card E=v.child.edges := by
    rw [Nat.card_eq_fintype_card]
    exact actual_child_card (Q:=Q)
  have hc : 2*(J9PrintedSchedule.arrayCard A)^2*p≤Nat.card E := nc.symm ▸ d.collision
  have hs : 2^A*J9PrintedSchedule.arrayCard A≤Nat.card E := nc.symm ▸ d.paddedSlots
  have hp : 0<precision.val := readPrecision.symm ▸ register_positive d t
  obtain ⟨P,L,win,mask,⟨recpt⟩,rows,fee⟩ := generate_stable_residents_and_native_rows
    v.child.host.network F rfl rfl rfl hFormat vs N.1 N.2 p q hq ha hcard d.degree.1 d.degree.2 hc hs
      i axis clock precision hp
  obtain ⟨target,tf⟩ := targets_from_registered_keys S fit rowKey colKey U
  let Y := prepareDescendant S q i.val axis U.rawRows U.rawCols precision
  have elem := framed_incidence_matches_format (a:=A) S fit rowKey colKey
  have total : (sourceIncidence S).steps=orderedIncidenceFee S :=
    congrArg Meter.steps (physical_incidence_from_frames S)
  have M : Y.result=some L := by
    unfold Y prepareDescendant
    dsimp only
    rw [elem,target]
    exact win
  refine ⟨⟨P,L,M,mask,readPrecision ▸ recpt,rows⟩,?_⟩
  unfold prepareDescendant
  dsimp only
  rw [elem,target]
  change (sourceIncidence S).steps+(writeTargets U.rawRows U.rawCols).steps+
    (prepareGreedySeats A q S.ownerWidth page (6*A) q i.val axis (vs.map F.target)
      (F.edges.map (fun e=>(encodeBits F.kR (F.rCode (F.row e)),encodeBits F.kC (F.cCode (F.col e)))))
      precision).steps+6≤_
  rw [total,←readPrecision]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left tf _) fee) 6

#print axioms VertexKeys.valid_order
#print axioms targets_from_registered_keys
#print axioms actual_frames_generate_descendant
end
end J6R49SourceLayout