import J6R12CollisionSource
import J6R11CollisionReindex

/-!
# Feeding the machine's chosen labels to the physical packing lemma

The labels handed to the rounded packet theorem are precisely those
on the final graph/vertex tapes. This does not count the subsequent
sorting and packet-writing operations.
-/

namespace J6R12CollisionPacking
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionSource
open J6R10Repack P11FullPacking J6R11Collision J6R11CollisionGreedy J6R11CollisionReindex

variable {E R C G : Type*} [Fintype E] [Fintype R] [Fintype C] [LinearOrder G] [Fintype G]
  {a : ℕ}

/-- The supplied input fields contain only row and column identifiers.
A charged copy inserts a zero/None assignment flag on each side. -/
def initGraph (kR kC : ℕ) (es : List (List Bool × List Bool)) : Meter (List EdgeTape) :=
  mapMeter (fun p => ⟨⟨⟨p.1,none⟩,⟨p.2,none⟩⟩,2*kR+2*kC+8⟩) es

omit [Fintype R] [Fintype C] [LinearOrder G] in
theorem initGraph_exact (F : Format E R C (Fin a→G)) :
    let es := F.edges.map (fun e => (encodeBits F.kR (F.rCode (F.row e)),
      encodeBits F.kC (F.cCode (F.col e))))
    let P := initGraph F.kR F.kC es
    P.result=F.graph (fun _ => none) ∧
      P.steps≤(2*F.kR+2*F.kC+14)*Fintype.card E := by
  let es := F.edges.map (fun e => (encodeBits F.kR (F.rCode (F.row e)),
    encodeBits F.kC (F.cCode (F.col e))))
  let m (p : List Bool × List Bool) : EdgeTape := ⟨⟨p.1,none⟩,⟨p.2,none⟩⟩
  have H := mapMeter_exact (fun p => ⟨m p,2*F.kR+2*F.kC+8⟩)
    m (2*F.kR+2*F.kC+8) es (fun _ _ => ⟨rfl,le_rfl⟩)
  change (initGraph F.kR F.kC es).result=es.map m ∧ _ at H
  refine ⟨H.1.trans ?_,?_⟩
  · dsimp only [es,Format.graph]
    rw [List.map_map]
    rfl
  · have he : es.length=Fintype.card E := by simp [es,F.graphEdges]
    change (initGraph F.kR F.kC es).steps≤_ at ⊢
    exact H.2.trans_eq (by rw [he])

theorem actual_labels_feed_packing (N : Network E R C)
    (F : Format E R C (Fin a→G)) (hrow : F.row=N.row) (hcol : F.col=N.col)
    (hG : Fintype.card G=64) (hb : F.b=6*a)
    (vs : List (R⊕C)) (hv : vs.Nodup) (hvs : ∀ i : R⊕C, i ∈ vs)
    (Δ : ℕ) (hr : ∀ v, Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v, Nat.card {e : E // N.col e=v}≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card E) :
    let es := F.edges.map (fun e => (encodeBits F.kR (F.rCode (F.row e)),
      encodeBits F.kC (F.cCode (F.col e))))
    let init := initGraph F.kR F.kC es
    let out := drive F.e F.kR F.kC F.b (vs.map F.target) init.result
    ∃ P : PhysicalPacking N a G,
      out.result.2=vs.map (fun i => F.label (Sum.elim P.rowLabel P.colLabel i)) ∧
      P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)) ∧
      init.steps+out.steps≤(2*F.kR+2*F.kC+14)*Fintype.card E+
        ((F.stepBound (2^(6*a))+2*F.b+6)*(Fintype.card R+Fintype.card C)+
          16*(F.b+1)*2^(6*a)+12*F.width+20) := by
  letI : Nonempty G := Fintype.card_pos_iff.mp (by omega)
  have rBound (v : R) : (fibre F.row v).card≤Δ := by
    rw [hrow,card_filter_fibre]
    exact hr v
  have cBound (v : C) : (fibre F.col v).card≤Δ := by
    rw [hcol,card_filter_fibre]
    exact hc v
  obtain ⟨z,_hgraph,hout,hvar,hcost⟩ := source_64 a hG F hb vs hv hvs Δ rBound cBound
  let z' := splitSample z
  have hg : varianceScore (declaredCell N z'.1 z'.2) ≤ 2*(Nat.card E:ℚ)*Δ := by
    rw [declared_variance_eq N z',Nat.card_eq_fintype_card,← hrow,← hcol]
    exact hvar
  obtain ⟨P,hRl,hCl,hCopy⟩ := actual_rounded_packing N hG z'.1 z'.2 Δ hg hcollision hslots
  obtain ⟨hi,hic⟩ := initGraph_exact F
  dsimp only
  rw [hi]
  refine ⟨P,?_,?_,Nat.add_le_add hic hcost⟩
  · rw [hout,hRl,hCl]
    congr 1
    funext b
    cases b <;> rfl
  · rw [hRl,hCl,hCopy]

#print axioms initGraph_exact
#print axioms actual_labels_feed_packing

end J6R12CollisionPacking
