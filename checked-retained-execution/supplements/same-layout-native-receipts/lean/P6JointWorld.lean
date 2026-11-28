import P6JointWorldCore
import P6JointGeometry
import P6JointCalibrated

namespace Paper6JointSeating
open scoped Polynomial Classical
open Polynomial J7SourceLabels J7PrintedParams J7LiteralGraph J9R21Implication
open J1PPrinted J8Physical NativeProbeRing J6R12Blueprint J9R20SameFile
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000

/-- Existence of one original rounded packing exhibiting both actual
native channels on the genuine cubic graph's triangle-replacement host. -/
theorem cubic_graph_same_certified_layout
    {V : Type} [LinearOrder V] [Fintype V] (B : SimpleGraph V) [DecidableRel B.Adj]
    (cub : Cubic B) (f' : ℤ[X]) (ell' created' : ℕ)
    (hf' : f'.Monic) (he' : 0<ell') (hc' : 0<created')
    (cfg : RootBounds (sourceSize (Fintype.card (Pin (Edge B)))) 3 f')
    [Fact (Irreducible (residuePoly f'))] :
    ∃ b, ∃ geom : JointSourceGeometry (atlas B cub)
      (stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin (Edge B))))) 0) b,
      JointLabelCollision (atlas B cub) geom ∧
      JointImplicationWorld (atlas B cub) geom f' ell' created' hf' he' := by
  have range := root_bounds_force_j9_range _ f' cfg
  obtain ⟨b,geom,hcollision⟩ := original_joint_geometry_with_label_collision (atlas B cub) range.2
  exact ⟨b,geom,hcollision,joint_literal_world_complete (atlas B cub) geom f' ell' created' hf'
    he' range.1 hc' range.2 cfg⟩

#print axioms JointImplicationWorld
#print axioms joint_literal_world_complete
#print axioms cubic_graph_same_certified_layout
end
end Paper6JointSeating




