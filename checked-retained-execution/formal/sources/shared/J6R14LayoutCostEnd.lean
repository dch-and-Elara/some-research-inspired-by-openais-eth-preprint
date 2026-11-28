import J6R14LayoutCostSource

/-! The actual paid labeler feeds the stable ordered-cell grouping and
least-multiple rounding. The returned labels are those of the very
same physical witness. This theorem does not yet assert the choice of
addresses within a cell or serialize the padded address space. -/

namespace J6R14LayoutCost
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionEdges J6R12CollisionSource J6R12CollisionBits J6R12CollisionGreedyStep
open J6R12CollisionPacking J6R12CollisionMenu
open J6R11Collision J6R11CollisionGreedy J6R11CollisionReindex J6R10Repack P11FullPacking

def groupedCopies (a kR kC b q : ℕ) (es : List EdgeTape) : Meter (List (Box Tagged) × List Bool) :=
  let t := orderedTape kR kC b q es
  let h := roundLoad a q t.result.2
  ⟨(t.result.1,h.result),t.steps+h.steps+4⟩

theorem groupedCopies_exact (a kR kC b q : ℕ) (hq : 0<q) (es : List EdgeTape)
    (hf : es.length<2^q) (he : ∀ t∈es,labelWidths b t) :
    let R := groupedCopies a kR kC b q es
    R.result.1=(allPairs b).map (boxSpec Tagged.edge q (tagSpec q 0 es)) ∧
    R.result.2.length=q+1 ∧
    bitsValue R.result.2=ceilCopies (2^a) (peak Tagged.edge (tagSpec q 0 es) (allPairs b)) ∧
    R.steps≤orderedTapeCap kR kC b q es.length+roundCap a q+4 := by
  let t := orderedTape kR kC b q es
  obtain ⟨hr,hl,hm,hc⟩ := orderedTape_exact kR kC b q hq es hf he
  obtain ⟨hw,hv,hs⟩ := roundLoad_exact a q t.result.2 hl
  refine ⟨hr,hw,?_,?_⟩
  · change bitsValue (roundLoad a q t.result.2).result=_
    rw [hv,show bitsValue t.result.2=_ from hm]
  · exact Nat.add_le_add_right (Nat.add_le_add hc hs) _

structure Layout where
  boxes : List (Box Tagged)
  copies : List Bool
  vertexLabels : List (List Bool)

def collisionToGroups (a e kR kC b q : ℕ) (vertices : List Target)
    (incidence : List (List Bool × List Bool)) : Meter Layout :=
  let p := initGraph kR kC incidence
  let g := drive e kR kC b vertices p.result
  let t := groupedCopies a kR kC b q g.result.1
  ⟨⟨t.result.1,t.result.2,g.result.2⟩,p.steps+g.steps+t.steps+6⟩

def collisionToGroupsCap {E R C A : Type*} [Fintype E] [Fintype A] [Fintype R] [Fintype C]
    (F : Format E R C A) (a q : ℕ) : ℕ :=
  (2*F.kR+2*F.kC+14)*Fintype.card E+
    ((F.stepBound (2^F.b)+2*F.b+6)*(Fintype.card R+Fintype.card C)+
      16*(F.b+1)*2^F.b+12*F.width+20)+
    (orderedTapeCap F.kR F.kC F.b q (Fintype.card E)+roundCap a q+4)+6

theorem collisionToGroups_exact {E R C G : Type*}
    [Fintype E] [Fintype R] [Fintype C] [LinearOrder G] [Fintype G] {a : ℕ}
    (N : Network E R C) (F : Format E R C (Fin a → G)) (hrow : F.row=N.row) (hcol : F.col=N.col)
    (hG : Fintype.card G=64) (hb : F.b=6*a)
    (vs : List (R⊕C)) (hn : vs.Nodup) (hall : ∀ v : R⊕C,v∈vs)
    (Δ q : ℕ) (hq : 0<q) (hfit : Fintype.card E<2^q)
    (hr : ∀ v, Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v, Nat.card {e : E // N.col e=v}≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card E) :
    let raw := F.edges.map (fun e =>
      (encodeBits F.kR (F.rCode (F.row e)),encodeBits F.kC (F.cCode (F.col e))))
    let T := collisionToGroups a F.e F.kR F.kC F.b q (vs.map F.target) raw
    ∃ z : R⊕C→Fin a→G, ∃ P : PhysicalPacking N a G,
      (∀ i,Sum.elim P.rowLabel P.colLabel i=z i) ∧
      T.result.vertexLabels=vs.map (fun i => F.label (z i)) ∧
      T.result.boxes=(allPairs F.b).map (boxSpec Tagged.edge q (tagSpec q 0 (F.graph (fun i=>some (z i))))) ∧
      T.result.copies.length=q+1 ∧ bitsValue T.result.copies=P.copies ∧
      T.steps≤collisionToGroupsCap F a q := by
  letI : Nonempty G := Fintype.card_pos_iff.mp (by omega)
  have hF : Fintype.card (Fin a→G)=2^F.b := by rw [hb,source_alphabet hG a]
  have hR (v : R) : (fibre F.row v).card≤Δ := by rw [hrow,card_filter_fibre]; exact hr v
  have hC (v : C) : (fibre F.col v).card≤Δ := by rw [hcol,card_filter_fibre]; exact hc v
  obtain ⟨z,hg,hl,hvar,htime⟩ := drive_exact F hF vs hn hall Δ hR hC
  obtain ⟨hinit,hic⟩ := initGraph_exact F
  let S := F.graph (fun i=>some (z i))
  have hs : S.length=Fintype.card E := by simp [S,Format.graph,F.graphEdges]
  have hfs : S.length<2^q := hs ▸ hfit
  obtain ⟨hr',hw,hcopy,hcost⟩ := groupedCopies_exact a F.kR F.kC F.b q hq S
    hfs (graphWord_widths F z)
  let z' := splitSample z
  have hg' : varianceScore (declaredCell N z'.1 z'.2)≤2*(Nat.card E:ℚ)*Δ := by
    rw [declared_variance_eq N z',Nat.card_eq_fintype_card,← hrow,← hcol]
    exact hvar
  obtain ⟨P,hpR,hpC,hpc⟩ := actual_rounded_packing N hG z'.1 z'.2 Δ hg' hcollision hslots
  have Hcell : (fun e => pairedWords a G (sourceCell F z e))=declaredCell N z'.1 z'.2 := by
    funext e
    simp only [sourceCell,hrow,hcol]
    rfl
  have hpeak : maxFiber (sourceCell F z)=maxFiber (declaredCell N z'.1 z'.2) := by
    rw [← Hcell,maxFiber_transport]
  have Hround : bitsValue (groupedCopies a F.kR F.kC F.b q S).result.2=P.copies := by
    change bitsValue (groupedCopies a F.kR F.kC F.b q S).result.2=_ at hcopy
    rw [hcopy,show peak Tagged.edge (tagSpec q 0 S) (allPairs F.b)=_ from peakSource_exact F hF z q,
      hpeak,hpc]
  refine ⟨z,P,?_,?_,?_,?_,?_,?_⟩
  · intro v
    rw [hpR,hpC]
    cases v <;> rfl
  · dsimp only [collisionToGroups]
    rw [hinit,hl]
  · dsimp only [collisionToGroups]
    rw [hinit,hg]
    exact hr'
  · dsimp only [collisionToGroups]
    rw [hinit,hg]
    exact hw
  · dsimp only [collisionToGroups]
    rw [hinit,hg]
    exact Hround
  · dsimp only [collisionToGroups]
    rw [hinit,hg]
    rw [hs] at hcost
    rw [hF] at htime
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hic htime) hcost) _

#print axioms groupedCopies_exact
#print axioms collisionToGroups_exact
end J6R14LayoutCost


