import J6R17ModeTapeHeaders
import J6R16ModeCostUniform

/-! The layout receipt specializes R14's paid greedy run. The exact
same copy count and all ordered-cell headers are handed downstream.
This does not change R14's stable within-cell edge ordering. -/
namespace J6R17ModeTape
open AOracleMachineTime AOracleMachineTimeTape
open J6R14LayoutCost J6R12CollisionGreedyStep J6R12CollisionPacking
open J6R12CollisionSource J6R11CollisionReindex J6R10Repack J6R15ModeCost

structure LayoutReceipt (a pages q edges : ℕ) where
  boxes : List ExportBox
  copies : Word q
  copiesMeaning : copies.val=pages
  headerMeaning : ∃ cs : List (P11FullPacking.Cell (Fin a) (Fin 64)),
    boxes.map headerOf=cs.map encodeHeader ∧ cs.Nodup ∧ (∀ c,c∈cs)
  boxCount : boxes.length=2^(6*a)*2^(6*a)
  rowCount : exportRows boxes=edges

theorem paidGreedy_layout_receipt {E R C : Type*} [Fintype E] [Fintype R] [Fintype C] {a : ℕ}
    (N : Network E R C) (F : Format E R C (Fin a→Fin 64))
    (hrow : F.row=N.row) (hcol : F.col=N.col) (hb : F.b=6*a)
    (hFormat : ∀ x,F.label x=coordinateLabel x)
    (vs : List (R⊕C)) (hn : vs.Nodup) (hall : ∀ v : R⊕C,v∈vs)
    (Δ q : ℕ) (hq : 0<q) (ha : a≤q) (hfit : Fintype.card E<2^q)
    (hr : ∀ v,Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v,Nat.card {e : E // N.col e=v}≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card E) :
    let raw := F.edges.map (fun e=>
      (encodeBits F.kR (F.rCode (F.row e)),encodeBits F.kC (F.cCode (F.col e))))
    let g := packGreedy a F.e F.kR F.kC F.b q (vs.map F.target) raw
    ∃ z : R⊕C→Fin a→Fin 64, ∃ P : PhysicalPacking N a (Fin 64),
      ∃ L : LayoutReceipt a P.copies (q+1) (Fintype.card E),
        (∀ j,Sum.elim P.rowLabel P.colLabel j=z j) ∧
        g.result.vertexLabels=vs.map (fun j=>F.label (z j)) ∧
        L.boxes=g.result.boxes ∧ L.copies.bits=g.result.copies ∧
        g.steps≤packGreedyCap a q F := by
  let raw := F.edges.map (fun e=>
    (encodeBits F.kR (F.rCode (F.row e)),encodeBits F.kC (F.cCode (F.col e))))
  let g := packGreedy a F.e F.kR F.kC F.b q (vs.map F.target) raw
  obtain ⟨z,P,hZ,hLabels,hQ,hCopy,hRel,_,hFee⟩ :=
    packGreedy_exact N F hrow hcol hb hFormat vs hn hall Δ q hq ha hfit hr hc hcollision hslots
  obtain ⟨cs,hH,hN,hA,hB,_,hR⟩ := packed_header_lift F hb z hRel
  exact ⟨z,P,⟨g.result.boxes,⟨g.result.copies,hQ⟩,hCopy,⟨cs,hH,hN,hA⟩,hB,hR⟩,
    hZ,hLabels,rfl,rfl,hFee⟩

#print axioms paidGreedy_layout_receipt
end J6R17ModeTape

