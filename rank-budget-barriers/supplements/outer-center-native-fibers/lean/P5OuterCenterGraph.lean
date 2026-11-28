import P5OuterCenterPacking
import P5OuterCenterClonePacking

set_option warningAsError true
namespace Paper5.OuterCenters
open scoped BigOperators Classical Polynomial
open P11FullPacking J6R10Repack J6R9PacketScopes HybridClosure

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (c : ∀ v,GraphCutMoments.degree E v=3)
variable (F : Finset (TriVertex V × TriVertex V))
variable (hF : F = replacedEdges E c)
variable (cub : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ}

include hF in
theorem exteriorMate_exact_graph (x : TriVertex V) :
    (x, exteriorMate E c x) ∈ F ∨ (exteriorMate E c x, x) ∈ F := by
  rw [hF]
  exact exteriorMate_edge E c x

noncomputable def actual_uncloned_section8_exact
    (P : PhysicalPacking (HybridDUncloned.network F cub) a (Fin 64))
    (K : ℕ) (hK : 1024*K ≤ 2^a) (ha : 512*a < Fintype.card (TriVertex V)) :=
  genuine_outer_child_fiber F cub P K (exteriorMate E c)
    (exteriorMate_exact_graph E c F hF)
    (budget_from_printed_packets F cub P K hK ha)

noncomputable def actual_cloned_section8_exact
    (P : PhysicalPacking (dNetwork F cub) a (Fin 64))
    (K : ℕ) (hK : 1024*K ≤ 2^a) (ha : 512*a < Fintype.card (TriVertex V)) :=
  Cloned.genuine_outer_child_fiber F cub P K (exteriorMate E c)
    (exteriorMate_exact_graph E c F hF)
    (Cloned.budget_from_printed_packets F cub P K hK ha)

#print axioms exteriorMate_exact_graph
#print axioms actual_uncloned_section8_exact
#print axioms actual_cloned_section8_exact
end Paper5.OuterCenters
