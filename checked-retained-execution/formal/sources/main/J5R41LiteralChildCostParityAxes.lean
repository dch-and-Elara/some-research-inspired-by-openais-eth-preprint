import J5R41LiteralChildCostAxes
import J5R41LiteralChildCostParityCore
import J6R10ReachablePrecision

/-! One parity vector for all mode orders of the same physical
full-precision call. The mode addresses are not changed to Mode i 1,
which would incorrectly delete the positive orders. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2600000

def parityEmbed (f : ℤ[X]) (ell : ℕ) : ZMod 2 →+* Residue f ell 1 :=
  (J6ActiveInterpolation.scalarIn 1 f ell).comp (AdjoinRoot.of (NativeProbeRing.liftPoly 1 f))

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G) {p : ℕ}

def allOdd (b : ColVertex P i g) (z : ColPort P i g b→Bool) :
    J45Parity.Bits (Tile P i×Bool) :=
  J45Parity.localFeature (fun _ q=>tileOf P i q.val) (fun _ q=>(ordinal P i q.val).val) b z

def modeFeature (m : Mode i p P.mask) : Tile P i×Bool :=
  (modeTile P i m,decide (m.order.val≠0))

def parityRoster (req : Finset (Mode i p P.mask)) (β : Mode i p P.mask→₀ℕ) :
    Finset (Tile P i×Bool) :=
  (req.filter (fun m=>0<β m)).image (modeFeature P i)

theorem actual_coordinate_parity (X : ColAssignments P i g) (m : Mode i p P.mask) :
    (sourceStat P i g ((colAssignmentsEquiv P i g) X) m : ZMod 2) =
       (∑ b,allOdd P i g b (X b)) (modeFeature P i m) := by
  let req : Finset (Mode i p P.mask) := {m}
  let u : Axis P i req := ⟨m,by simp [req]⟩
  change (sourceStat P i g ((colAssignmentsEquiv P i g) X) u.val:ZMod 2)=_
  rw [←source_coordinate_exact P i g req X u]
  simp only [Finset.sum_apply,J45Cost.sourceIncrement,Nat.cast_sum]
  refine Finset.sum_congr rfl fun b _=>?_
  unfold allOdd modeFeature
  rw [←J45Parity.localMode_feature]
  refine Finset.sum_congr rfl fun q _=>?_
  change ((if X b q then (if tileOf P i q.val=modeTile P i m then
    (ordinal P i q.val).val^m.order.val else 0) else 0 : ℕ) : ZMod 2) =
      if tileOf P i q.val=modeTile P i m ∧ X b q=true then
        ((ordinal P i q.val).val:ZMod 2)^m.order.val else 0
  by_cases h : tileOf P i q.val=modeTile P i m <;>
    cases z : X b q <;> simp [h,z,Nat.cast_pow]

theorem actual_child_moment_parity
    (req : Finset (Mode i p P.mask)) (β : Mode i p P.mask→₀ℕ)
    (X : ColAssignments P i g) :
    (∏ m∈req,(sourceStat P i g ((colAssignmentsEquiv P i g) X) m:Residue f ell 1)^β m) =
      ∏ d∈parityRoster P i req β,parityEmbed f ell ((∑ b,allOdd P i g b (X b)) d) := by
  let F := ∑ b,allOdd P i g b (X b)
  let φ := parityEmbed f ell
  change _ = ∏ d∈parityRoster P i req β,φ (F d)
  calc
    _=∏ m∈req,φ (F (modeFeature P i m))^β m := by
      refine Finset.prod_congr rfl fun m _=>?_
      dsimp only [F,φ]
      rw [←actual_coordinate_parity P i g X m,map_natCast]
    _=φ (∏ m∈req,F (modeFeature P i m)^β m) := by rw [map_prod]; simp only [map_pow]
    _=φ (∏ d∈parityRoster P i req β,F d) := by
      exact congrArg φ (J45Parity.collapse_powers req (modeFeature P i) β F)
    _=_ := by rw [map_prod]

#print axioms parityEmbed
#print axioms actual_coordinate_parity
#print axioms actual_child_moment_parity
end
end J5R41LiteralChildCost

