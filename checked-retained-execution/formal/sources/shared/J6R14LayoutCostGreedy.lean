import J6R14LayoutCostFixed

/-! Paid raw incidence to collision-selected labels and stable
physical address export. The original abstract witness supplies the
certified capacity; its arbitrary within-cell bijection is not used
as a machine step. -/
namespace J6R14LayoutCost
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionPacking J6R12CollisionSource J6R12CollisionMenu
open J6R11Collision J6R11CollisionGreedy J6R11CollisionReindex J6R10Repack P11FullPacking

structure GreedyPackedTape where
  boxes : List ExportBox
  copies : List Bool
  vertexLabels : List (List Bool)

def packGreedy (a e kR kC b q : ℕ) (vertices : List Target)
    (incidence : List (List Bool × List Bool)) : Meter GreedyPackedTape :=
  let p := initGraph kR kC incidence
  let g := drive e kR kC b vertices p.result
  let t := packFixed kR kC b q a g.result.1
  ⟨⟨t.result.boxes,t.result.copies,g.result.2⟩,p.steps+g.steps+t.steps+6⟩

def packGreedyCap {E R C : Type*} [Fintype E] [Fintype R] [Fintype C] (a q : ℕ)
    (F : Format E R C (Fin a→Fin 64)) : ℕ :=
  (2*F.kR+2*F.kC+14)*Fintype.card E+
    ((F.stepBound (2^F.b)+2*F.b+6)*(Fintype.card R+Fintype.card C)+
      16*(F.b+1)*2^F.b+12*F.width+20)+
    packFixedCap F.kR F.kC F.b q a (Fintype.card E)+6

theorem packGreedy_exact {E R C : Type*} [Fintype E] [Fintype R] [Fintype C] {a : ℕ}
    (N : Network E R C) (F : Format E R C (Fin a→Fin 64))
    (hrow : F.row=N.row) (hcol : F.col=N.col)
    (hb : F.b=6*a) (hFormat : ∀ x,F.label x=coordinateLabel x)
    (vs : List (R⊕C)) (hn : vs.Nodup) (hall : ∀ v : R⊕C,v∈vs)
    (Δ q : ℕ) (hq : 0<q) (ha : a≤q) (hfit : Fintype.card E<2^q)
    (hr : ∀ v, Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v, Nat.card {e : E // N.col e=v}≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card E) :
    let raw := F.edges.map (fun e =>
      (encodeBits F.kR (F.rCode (F.row e)),encodeBits F.kC (F.cCode (F.col e))))
    let t := packGreedy a F.e F.kR F.kC F.b q (vs.map F.target) raw
    ∃ z : R⊕C→Fin a→Fin 64, ∃ P : PhysicalPacking N a (Fin 64),
      (∀ i,Sum.elim P.rowLabel P.colLabel i=z i) ∧
      t.result.vertexLabels=vs.map (fun i => F.label (z i)) ∧
      t.result.copies.length=q+1 ∧ bitsValue t.result.copies=P.copies ∧
      List.Forall₂ (boxFaithful a P.copies q) (sourceBoxes F z q) t.result.boxes ∧
      (t.result.boxes.flatMap (fun x=>x.rows.map Seated.tag)).Perm
        (tagSpec q 0 (F.graph (fun j=>some (z j)))) ∧
      t.steps≤packGreedyCap a q F := by
  have hG : Fintype.card (Fin 64)=64 := by simp
  have hF : Fintype.card (Fin a→Fin 64)=2^F.b := by rw [hb,source_alphabet hG a]
  have hR (v : R) : (fibre F.row v).card≤Δ := by rw [hrow,card_filter_fibre]; exact hr v
  have hC (v : C) : (fibre F.col v).card≤Δ := by rw [hcol,card_filter_fibre]; exact hc v
  obtain ⟨z,hg,hl,hvar,ht⟩ := drive_exact F hF vs hn hall Δ hR hC
  obtain ⟨hi,hic⟩ := initGraph_exact F
  obtain ⟨hQ,hPc,hSeats,hCon,hTime⟩ := packFixed_exact F hb hFormat z q hq ha hfit
  let xy := splitSample z
  have hV : varianceScore (declaredCell N xy.1 xy.2)≤2*(Nat.card E:ℚ)*Δ := by
    rw [declared_variance_eq N xy,Nat.card_eq_fintype_card,← hrow,← hcol]
    exact hvar
  obtain ⟨P,hProw,hPcol,hPcopy⟩ := actual_rounded_packing N hG xy.1 xy.2 Δ hV hcollision hslots
  have heq : (fun e => pairedWords a (Fin 64) (sourceCell F z e))=declaredCell N xy.1 xy.2 := by
    funext e
    simp only [sourceCell,hrow,hcol]
    rfl
  have hpc : sourcePages F z q=P.copies := by
    rw [sourcePages,peakSource_exact F hF z q,hPcopy,← heq,maxFiber_transport]
  have hPose (i : R⊕C) : Sum.elim P.rowLabel P.colLabel i=z i := by
    rw [hProw,hPcol]
    cases i <;> rfl
  refine ⟨z,P,hPose,?_,?_,?_,?_,?_,?_⟩ <;>
    dsimp only [packGreedy] <;> rw [hi]
  · exact hl
  · rw [hg]
    exact hQ
  · rw [hg,← hpc]
    exact hPc
  · rw [hg,← hpc]
    exact hSeats
  · rw [hg]
    exact hCon
  · rw [hg]
    rw [hF] at ht
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hic ht) hTime) _

#print axioms packGreedy_exact
end J6R14LayoutCost


