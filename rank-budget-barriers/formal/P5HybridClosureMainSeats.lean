import P5HybridClosureMain
import J1MainSourceBridge
import J6R11CollisionReindex

/-! Literal MAIN copied-auxiliary input seats. No free occupancy oracle:
the original incidence cell and its distinct copy address are linked. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open J1MainSourceLabels J1MainSourceCollision J1MainSourceBridge J1MainSourcePlacement
open DiagonalAbundance (Draw)

variable {V Q G : Type*} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
  [Fintype G] [Nonempty G]

noncomputable abbrev triangleIncidenceData (F : Finset (TriVertex V×TriVertex V))
    (reg : ∀v,GraphCutMoments.degree F v=3) (t : Q) (z : MainPrimitives F Q→G) :=
  originalData t triangleTie (cloneOwner F reg) (cloneFactor F) z

def MainSeatCertificate (F : Finset (TriVertex V×TriVertex V))
    (reg : ∀v,GraphCutMoments.degree F v=3) (t : Q) (z : MainPrimitives F Q→G) (cap : ℚ) : Prop :=
    let D := triangleIncidenceData F reg t z
    (copies D:ℚ)≤cap ∧
    Function.Injective (position D (copies D) (copies_suffice D)) ∧
    ∀e : MainClonedCNF.Port F,
      occupied D (copies D) (copies_suffice D) (copyIndex D (copies D) (copies_suffice D) e)
        (D.cell e) = some (cloneOwner F reg e)

theorem actual_main_seats (F : Finset (TriVertex V×TriVertex V))
    (reg : ∀v,GraphCutMoments.degree F v=3) (t : Q) (z : MainPrimitives F Q→G)
    (cap : ℚ) (hcap : ∀u : Draw Q G,
      load (literalCell t triangleTie (cloneOwner F reg) (cloneFactor F) z) u≤cap) :
    MainSeatCertificate F reg t z cap := by
  let D := triangleIncidenceData F reg t z
  let count := fun u : Draw Q G => Fintype.card (CellFibre D u)
  obtain ⟨u,_,hu⟩ := Finset.exists_max_image Finset.univ count Finset.univ_nonempty
  have hb : copies D≤count u := copies_budget D _ (fun v=>hu v (Finset.mem_univ _))
  have hc (v : Draw Q G) : (count v:ℚ)=load D.cell v := by
    unfold count
    rw [←Nat.card_eq_fintype_card]
    exact J6R11CollisionReindex.card_fibre_load D.cell v
  have hb' : (copies D:ℚ)≤count u := by exact_mod_cast hb
  refine ⟨hb'.trans ?_,position_injective D _ _,?_⟩
  · rw [hc]
    exact hcap u
  · exact occupied_at D _ _

#print axioms actual_main_seats
end Paper5.HybridClosure