import J6R48RawRouteFrame
import J6R32ChildResidentTransferFormat

/-! The actual R41 output already carries both endpoints of its
precise physical child graph. Read those records in order to generate
the next greedy incidence input; no fresh function of an edge is
evaluated by the byte program. -/
namespace J6R49SourceLayout
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes
open J6R32ChildResidentTransfer J6R48RawRoute J6R12CollisionGreedyStep J6R12CollisionMenu
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2600
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option Elab.async false

def framedIncidenceFee {w owner key prec page : ℕ} (x : FramedEdge w owner key prec page) : ℕ :=
  (3*owner+1)+originFee key prec page x.right.origin.pageKey.isSome+
    originFee key prec page x.left.origin.pageKey.isSome+2*(3*w+1)+
    (3*x.left.body.length+1)+(3*x.right.body.length+1)+12

abbrev Incidence := List Bool×List Bool

/-- Copy the two endpoint words; the discarded opaque fields are
traversed and charged, without parsing their variable-length codes. -/
def readFramedIncidence {w owner key prec page : ℕ} (x : FramedEdge w owner key prec page) :
    Meter (Option Incidence) :=
  let old := copyFixed x.oldOwner
  let fresh := copyOrigin x.right.origin
  let prev := copyOrigin x.left.origin
  let leftID := copyFixed x.left.id.edge
  let rightID := copyFixed x.right.id.edge
  let left := copyBytes x.left.body
  let right := copyBytes x.right.body
  ⟨fresh.result.pageKey.map (fun p=>(old.result.bits,p.bits)),
    old.steps+fresh.steps+prev.steps+leftID.steps+rightID.steps+left.steps+right.steps+12⟩

theorem framed_incidence_row_exact {w owner key prec page : ℕ}
    (x : FramedEdge w owner key prec page) :
    readFramedIncidence x =
      ⟨x.right.origin.pageKey.map (fun p=>(x.oldOwner.bits,p.bits)),framedIncidenceFee x⟩ := by
  simp only [readFramedIncidence,copy_fixed_exact,copy_origin_exact,copyBytes_exact,framedIncidenceFee]
  apply congrArg₂ (fun v n=>(⟨v,n⟩ : Meter (Option Incidence)))
  · rfl
  · omega

def readFramedRows {w owner key prec page : ℕ} :
    List (FramedEdge w owner key prec page) → Meter (Option (List Incidence))
  | []=>⟨some [],4⟩
  | x::xs=>
    let h := readFramedIncidence x
    match h.result with
    | none=>⟨none,h.steps+4⟩
    | some edge=>
      let t := readFramedRows xs
      ⟨t.result.map (edge::·),h.steps+t.steps+6⟩

theorem framed_incidence_rows_exact {E : Type*} {w owner key prec page : ℕ} (es : List E)
    (frame : E→FramedEdge w owner key prec page) (row : E→Incidence)
    (sound : ∀ e,(frame e).right.origin.pageKey.map (fun p=>((frame e).oldOwner.bits,p.bits))=some (row e)) :
    readFramedRows (es.map frame)=
      ⟨some (es.map row),4+(es.map (fun e=>framedIncidenceFee (frame e)+6)).sum⟩ := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,readFramedRows,framed_incidence_row_exact,sound,ih,
      Option.map_some,List.sum_cons]
    apply congrArg₂ (fun v n=>(⟨v,n⟩ : Meter (Option (List Incidence))))
    · rfl
    · omega

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs Q previous)
local notation "E" => v.child.host.Edge
local notation "R" => v.child.host.Row
local notation "D" => v.child.host.Col

def physicalChildRows : R ≃ OldAt T v :=
  Equiv.cast (congrArg PhysicalHost.Row (actual_ticket_host T v))

def physicalChildCols : D ≃ PageAt T v :=
  Equiv.cast (congrArg PhysicalHost.Col (actual_ticket_host T v))

private theorem cast_row {H K : PhysicalHost f ell} (h : H=K) (x : H.Row) :
    Equiv.cast (congrArg (fun A : PhysicalHost f ell=>A.Row⊕A.Col) h) (.inl x)=
      .inl (Equiv.cast (congrArg PhysicalHost.Row h) x) := by
  subst K
  rfl

private theorem cast_col {H K : PhysicalHost f ell} (h : H=K) (x : H.Col) :
    Equiv.cast (congrArg (fun A : PhysicalHost f ell=>A.Row⊕A.Col) h) (.inr x)=
      .inr (Equiv.cast (congrArg PhysicalHost.Col h) x) := by
  subst K
  rfl

theorem actual_child_endpoint_names (e : E) :
    (physicalChildRows (T:=T) (v:=v) (v.child.host.network.row e)).val=
      owner v.parent.host.network (childHalves T v e).val ∧
    physicalChildCols (T:=T) (v:=v) (v.child.host.network.col e)=
      atPacket (layout T v) (edge (childHalves T v e).val) := by
  obtain ⟨hr,hc⟩ := actual_child_half_endpoints T v e
  have L := cast_row (actual_ticket_host T v) (v.child.host.network.row e)
  have H := cast_col (actual_ticket_host T v) (v.child.host.network.col e)
  exact ⟨congrArg Subtype.val (Sum.inl.inj (L.symm.trans hr)),Sum.inr.inj (H.symm.trans hc)⟩

def nativeRowKey (x : R) : Word S.ownerWidth := S.oldKey (physicalChildRows (T:=T) (v:=v) x).val
def nativeColKey (y : D) : Word page := S.pageKey (physicalChildCols (T:=T) (v:=v) y)

theorem framed_edge_names_actual_endpoints (e : E) :
    (frameOf S e).oldOwner=nativeRowKey S (v.child.host.network.row e) ∧
    (frameOf S e).right.origin.pageKey=some (nativeColKey S (v.child.host.network.col e)) := by
  rcases actual_child_endpoint_names (T:=T) (v:=v) e with ⟨row,col⟩
  constructor
  · change S.oldKey (owner v.parent.host.network (childHalves T v e).val)=_
    rw [nativeRowKey,row]
  · change some (S.pageKey (atPacket (layout T v) (edge (childHalves T v e).val)))=_
    rw [nativeColKey,col]

def sourceIncidence : Meter (Option (List Incidence)) :=
  match S.write.result.framed with
  | none=>⟨none,3⟩
  | some xs=>
    let out := readFramedRows xs
    ⟨out.result,out.steps+3⟩

theorem physical_incidence_from_frames :
    sourceIncidence S =
      ⟨some ((childOrder S).map (fun e=>((nativeRowKey S (v.child.host.network.row e)).bits,
        (nativeColKey S (v.child.host.network.col e)).bits))),
        7+((childOrder S).map (fun e=>framedIncidenceFee (frameOf S e)+6)).sum⟩ := by
  unfold sourceIncidence
  rw [source_framed_in_child_order]
  dsimp only
  have sound (e : E) := framed_edge_names_actual_endpoints S e
  have row (e : E) :
      (frameOf S e).right.origin.pageKey.map (fun p=>((frameOf S e).oldOwner.bits,p.bits))=
        some ((nativeRowKey S (v.child.host.network.row e)).bits,
          (nativeColKey S (v.child.host.network.col e)).bits) := by
    rw [(sound e).1,(sound e).2]
    rfl
  rw [framed_incidence_rows_exact (childOrder S) (frameOf S) _ row]
  apply congrArg₂ (fun v n=>(⟨v,n⟩ : Meter (Option (List Incidence))))
  · rfl
  · simp only
    omega

local instance finiteActualChild : Fintype E := v.child.host.finiteEdge

include Q in
theorem actual_child_card : Fintype.card E=v.child.edges := by
  rw [Fintype.card_congr (actualEdgeOrder T v Q.native.physical).symm,Fintype.card_fin]

def nativeFormat {a q : ℕ} (fit : v.child.edges<2^q)
    (rowKey : Function.Injective S.oldKey) (colKey : Function.Injective S.pageKey) :
    Format E R D (Fin a→Fin 64) :=
  childFormat v.child.host.network q ((actual_child_card (Q:=Q)).trans_lt fit)
    (childOrder S) (child_order_complete S).1 (child_order_complete S).2
    (nativeRowKey S) (nativeColKey S)
      (rowKey.comp (Subtype.val_injective.comp (physicalChildRows (T:=T) (v:=v)).injective))
      (colKey.comp (physicalChildCols (T:=T) (v:=v)).injective)

theorem framed_incidence_matches_format {a q : ℕ} (fit : v.child.edges<2^q)
    (rowKey : Function.Injective S.oldKey) (colKey : Function.Injective S.pageKey) :
    let F := nativeFormat (a:=a) S fit rowKey colKey
    (sourceIncidence S).result=some (F.edges.map (fun e=>
      (encodeBits F.kR (F.rCode (F.row e)),encodeBits F.kC (F.cCode (F.col e))))) := by
  rw [physical_incidence_from_frames]
  dsimp only
  congr 1
  apply List.map_congr_left
  intro e _
  exact Prod.ext
    (congrArg Word.bits (valued_word (nativeRowKey S (v.child.host.network.row e)))).symm
    (congrArg Word.bits (valued_word (nativeColKey S (v.child.host.network.col e)))).symm

#print axioms framed_incidence_row_exact
#print axioms framed_incidence_rows_exact
#print axioms actual_child_endpoint_names
#print axioms framed_edge_names_actual_endpoints
#print axioms physical_incidence_from_frames
#print axioms actual_child_card
#print axioms framed_incidence_matches_format
end
end J6R49SourceLayout