import J6R14LayoutCostTape
import J6R14LayoutCostConserve

/-! The fixed-order entry point: the actual supplied fully-labeled
graph uses the same exporter as the graph produced by the greedy run.
This is the relevant interface when a reduction chooses its own labels
and stable tie order rather than running the greedy computation. -/
namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionPacking J6R12CollisionSource
open J6R11CollisionReindex P11FullPacking

variable {E R C : Type*} [Fintype E] {a : ℕ}

def sourceBoxes (F : Format E R C (Fin a→Fin 64)) (z : R⊕C→Fin a→Fin 64) (q : ℕ) :
    List (Box Tagged) :=
  (allPairs F.b).map (boxSpec Tagged.edge q (tagSpec q 0 (F.graph (fun x=>some (z x)))))

def sourcePages (F : Format E R C (Fin a→Fin 64)) (z : R⊕C→Fin a→Fin 64) (q : ℕ) : ℕ :=
  ceilCopies (2^a) (peak Tagged.edge (tagSpec q 0 (F.graph (fun x=>some (z x)))) (allPairs F.b))

theorem sourceGraph_len (F : Format E R C (Fin a→Fin 64)) (z : R⊕C→Fin a→Fin 64) :
    (F.graph (fun x=>some (z x))).length=Fintype.card E := by
  simp [Format.graph,F.graphEdges]

theorem sourceBoxes_valid (F : Format E R C (Fin a→Fin 64)) (hb : F.b=6*a)
    (hFormat : ∀ x,F.label x=coordinateLabel x) (z : R⊕C→Fin a→Fin 64)
    (q : ℕ) (hq : Fintype.card E<2^q) :
    ∀ B∈sourceBoxes F z q,validBox a (sourcePages F z q) q B := by
  let T := tagSpec q 0 (F.graph (fun x=>some (z x)))
  have hL : T.length<2^q := by rwa [show T.length=_ from tagSpec_length _ _ _,sourceGraph_len]
  have hS : Fintype.card (Fin a→Fin 64)=2^F.b := by
    rw [hb,J6R12CollisionMenu.source_alphabet (G:=Fin 64) (by simp) a]
  intro B he
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp he
  obtain ⟨x,H⟩ := codePair_cover F hS k hk
  have Hk : k=wordCell (pairedWords a (Fin 64) x) := by
    dsimp only [wordCell,pairedWords,Equiv.coe_fn_mk]
    rw [← H,codePair,hFormat,hFormat]
  refine ⟨pairedWords a (Fin 64) x,Hk,(List.length_filter_le ..).trans_lt hL,?_,?_⟩
  · have hh := bucket_le_peak Tagged.edge T (allPairs F.b) k hk
    exact hh.trans (rounded_capacity _ _ (by positivity)).1
  · intro v hv
    exact of_decide_eq_true (List.mem_filter.mp hv).2

theorem sourceBoxes_counts (F : Format E R C (Fin a→Fin 64))
    (z : R⊕C→Fin a→Fin 64) (q : ℕ) :
    (sourceBoxes F z q).length=2^F.b*2^F.b ∧ rowsOnTape (sourceBoxes F z q)=Fintype.card E := by
  refine ⟨by simp only [sourceBoxes,List.length_map,allPairs_len],?_⟩
  have H := (graph_grouped_conserves F z q).length_eq
  change rowsOnTape (sourceBoxes F z q)=(tagSpec q 0 (F.graph (fun x=>some (z x)))).length at H
  rw [H,tagSpec_length,sourceGraph_len]

structure PackedTape where
  boxes : List ExportBox
  copies : List Bool

def packFixed (kR kC b q a : ℕ) (es : List EdgeTape) : Meter PackedTape :=
  let g := groupedCopies a kR kC b q es
  let w := exportTape kR kC b q a g.result.1
  ⟨⟨w.result,g.result.2⟩,g.steps+w.steps+6⟩

def packFixedCap (kR kC b q a M : ℕ) : ℕ :=
  orderedTapeCap kR kC b q M+roundCap a q+4+
    exportTapeCap kR kC b q a (2^b*2^b) M+6

theorem packFixed_exact (F : Format E R C (Fin a→Fin 64)) (hb : F.b=6*a)
    (hFormat : ∀ x,F.label x=coordinateLabel x) (z : R⊕C→Fin a→Fin 64)
    (q : ℕ) (hq : 0<q) (ha : a≤q) (hf : Fintype.card E<2^q) :
    let es := F.graph (fun x=>some (z x))
    let p := packFixed F.kR F.kC F.b q a es
    p.result.copies.length=q+1 ∧ bitsValue p.result.copies=sourcePages F z q ∧
    List.Forall₂ (boxFaithful a (sourcePages F z q) q) (sourceBoxes F z q) p.result.boxes ∧
    (p.result.boxes.flatMap (fun x=>x.rows.map Seated.tag)).Perm (tagSpec q 0 es) ∧
    p.steps≤packFixedCap F.kR F.kC F.b q a (Fintype.card E) := by
  let es := F.graph (fun x=>some (z x))
  let g := groupedCopies a F.kR F.kC F.b q es
  obtain ⟨hg,hL,hM,hC⟩ := groupedCopies_exact a F.kR F.kC F.b q hq es
    (by rw [show es.length=_ from sourceGraph_len F z]; exact hf) (graphWord_widths F z)
  have H := exportTape_exact F.kR F.kC F.b q a (sourcePages F z q) hq ha
    (sourceBoxes F z q) (sourceBoxes_valid F hb hFormat z q hf)
  change g.result.1=sourceBoxes F z q at hg
  let W := exportTape F.kR F.kC F.b q a g.result.1
  obtain ⟨wrel,wCost⟩ := H
  have hrel : List.Forall₂ (boxFaithful a (sourcePages F z q) q) (sourceBoxes F z q) W.result := by
    change List.Forall₂ _ _ (exportTape F.kR F.kC F.b q a g.result.1).result
    rw [hg]
    exact wrel
  refine ⟨hL,hM,hrel,?_,?_⟩
  · change (W.result.flatMap _).Perm _
    rw [exportTape_conserves hrel]
    exact graph_grouped_conserves F z q
  · change g.steps+W.steps+6≤_
    rw [sourceBoxes_counts F z q |>.1,sourceBoxes_counts F z q |>.2] at wCost
    have hw : W.steps≤exportTapeCap F.kR F.kC F.b q a (2^F.b*2^F.b) (Fintype.card E) := by
      change (exportTape F.kR F.kC F.b q a g.result.1).steps≤_
      rw [hg]
      exact wCost
    change g.steps≤_ at hC
    rw [show es.length=_ from sourceGraph_len F z] at hC
    exact Nat.add_le_add_right (Nat.add_le_add hC hw) 6

#print axioms sourceBoxes_valid
#print axioms sourceBoxes_counts
#print axioms packFixed_exact
end J6R14LayoutCost



