import A4R45FlagProduct
import A4R45NativeGeometry
/-! Identify the primitive completed zero-mode sum on the actual A4
sparse host with the literal signed predecessor register in A6. -/
namespace A4R45LiteralValue
open scoped BigOperators Polynomial
open Acquisition A4R45LiteralNetwork A4R45LiteralTables AAcquisitionCost
open J6R10Repack P11FullPacking V8NativeMessage.N7LiteralSupport
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3300000
set_option maxRecDepth 1600

noncomputable section
variable {V₂ V₃ U C G : Type} [Fintype V₂] [Fintype V₃] [Fintype U] [Fintype C]
variable [LinearOrder G] [Fintype G] {a : ℕ}
variable {K : Type} [CommRing K]
local notation "W" => Wire V₂ V₃ U
local notation "N" => network (V₂:=V₂) (V₃:=V₃) (U:=U)

variable (P : PhysicalPacking (A4R45LiteralNetwork.network (V₂:=V₂) (V₃:=V₃) (U:=U)) a G)
variable (seat : A4R45LiteralNetwork.Wire V₂ V₃ U ≃ Physical a P.copies G)
variable (same : ∀ w : A4R45LiteralNetwork.Wire V₂ V₃ U,P.seat w=seat w)
include same

theorem native_flat_eq_literal_predecessor (cols : Var V₂ V₃ U ≃ C)
    [DecidableEq V₂] [DecidableEq V₃] [DecidableEq U] :
    flatSigned P (-1) (-1:K) trueFlags =
      literalShiftedRegister (coverTables (K:=K)) cols (wirePred seat) := by
  classical
  rw [literal_cubes_sum_columns_first P (-1) (-1:K) trueFlags]
  unfold literalShiftedRegister
  refine Finset.sum_congr (Finset.ext fun _ => by simp only [Finset.mem_univ]) ?_
  intro X _
  rw [Finset.mul_sum]
  refine Finset.sum_congr (Finset.ext fun _ => by simp only [Finset.mem_univ]) ?_
  intro Y _
  unfold flatTerm
  rw [actual_flags_product cols X Y]
  change (rowProduct (coverTables (K:=K)) (fun i => Y (i,true)) *
    equalityTensor (cols ∘ (Prod.fst : W→Var V₂ V₃ U)) X) *
    (∏ r : W,LiteralPortCompiler.affine (Y r)
      ((-1:K)*wholeShiftBit P K (-1) (Sum.elim Y X) r)) = _
  have shift : (∏ r : W,LiteralPortCompiler.affine (Y r)
       ((-1:K)*wholeShiftBit P K (-1) (Sum.elim Y X) r)) =
     ∏ r : W,lag (Y r) (-bit (readPredecessor (wirePred seat r) X)) :=
    Finset.prod_congr rfl fun r _ => A4R45NativeGeometry.wire_lag P seat same X Y r
  rw [shift]
  ring

#print axioms native_flat_eq_literal_predecessor
end
end A4R45LiteralValue
