import J1PhysicalHost
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! The exterior matching in the triangle-replacement model need not be
postulated. For any finite simple cubic graph, enumerate each vertex's three
ports by its actual neighbors and find the opposite port at the neighbor. -/
namespace J1PhysicalCubic
open J1PhysicalHost
variable {B : Type*} [Fintype B] [DecidableEq B]
variable (G : SimpleGraph B) [DecidableRel G.Adj]
variable (hCub : ∀ b, G.degree b = 3)

noncomputable def portAt (b : B) : G.neighborSet b ≃ Fin 3 :=
  Fintype.equivFinOfCardEq ((G.card_neighborSet_eq_degree b).trans (hCub b))

noncomputable def crossPort (v : Vertex B) : Vertex B :=
  let n := (portAt G hCub v.1).symm v.2
  (n.val,portAt G hCub n.val ⟨v.1,G.symm n.property⟩)

omit [DecidableEq B] in
theorem crosses (v : Vertex B) : (crossPort G hCub v).1 ≠ v.1 := by
  intro h
  have he : G.Adj v.1 (crossPort G hCub v).1 :=
    ((portAt G hCub v.1).symm v.2).property
  rw [h] at he
  exact G.loopless _ he

omit [DecidableEq B] in
theorem reciprocal : Function.Involutive (crossPort G hCub) := by
  rintro ⟨b,i⟩
  let n := (portAt G hCub b).symm i
  let back : G.neighborSet n.val := ⟨b,G.symm n.property⟩
  have e₁ : crossPort G hCub (b,i) = (n.val,portAt G hCub n.val back) := rfl
  rw [e₁]
  let decode (u : G.neighborSet n.val) : Vertex B :=
    (u.val,portAt G hCub u.val ⟨n.val,G.symm u.property⟩)
  change decode ((portAt G hCub n.val).symm (portAt G hCub n.val back)) = (b,i)
  rw [Equiv.symm_apply_apply]
  have hh : decode back = (b,portAt G hCub b n) := rfl
  rw [hh]
  exact congrArg (fun j => (b,j)) ((portAt G hCub b).apply_symm_apply i)

/-- The actual subdivision ports of any finite simple cubic base graph. -/
noncomputable def ofCubic : Match B where
  mate := crossPort G hCub
  inv := reciprocal G hCub
  cross := crosses G hCub

theorem physical_degree (v : Vertex B) :
    GraphCutMoments.degree (edges (ofCubic G hCub)) v = 3 :=
  degree_eq_three _ v

#print axioms crosses
#print axioms reciprocal
#print axioms physical_degree

end J1PhysicalCubic
