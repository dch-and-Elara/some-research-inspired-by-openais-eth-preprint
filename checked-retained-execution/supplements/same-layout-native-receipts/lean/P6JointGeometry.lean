import P6JointGeometryModel
import P6JointPrintedSeats
import J9R20SameFilePublicWorld

namespace Paper6JointSeating
open scoped Classical BigOperators Polynomial
open Polynomial J7SourceLabels J7PrintedParams J7PrintedParamsGraph J7ToJ8Incidence J7ToJ8Layout
open J7SeatSource P11FullPacking J7SeatPacking J7SeatRounded J7ToJ8Canonical
open J6R10Repack J6R9PacketScopes J8Physical J6R14SpecializedBox J1PPrinted J9R20SameFile

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool ≃ Pin Pair×Fin 3)
local notation "N₀" => Fintype.card (Pin Pair)
local notation "R" => Subdivision Pair (OrdinaryRow Pair H)
local notation "E" => J8Physical.Wire R
local notation "T" => (column ends cycle)
local notation "G" => Fin 64
local notation "D" => PrintedOld Pair H
local notation "U" => Clones Pair

def JointLabelCollision {a b : ℕ} (geom : JointSourceGeometry ends a b) : Prop :=
  J6R10Repack.varianceScore
    (declaredCell (J7R13.network Prod.fst T) geom.wordsR geom.wordsC) ≤
      2*(Nat.card (Wires Pair H):ℚ)*rootDelta (sourceSize N₀)

theorem original_joint_geometry_with_label_collision
    (large : 2^(9*131072-1) < sourceSize N₀) :
    ∃ b, ∃ geom : JointSourceGeometry ends (stepA (Nat.clog 2 (sourceSize N₀)) 0) b,
      JointLabelCollision ends geom := by
  let t := rootT (sourceSize N₀)
  have hU : 0<rootU (sourceSize N₀) := lt_of_lt_of_le (by decide : (0:ℕ)<9) (u_large _ large)
  rw [J7R13.root_bits_same _ hU]
  obtain ⟨z,hcollision,hcap,cross,j,keep,hd,hcount,preserve,hseat,hnp,hr⟩ :=
    literalJointPrintedSeats ends large
  let b := ceilCopies (2^(t+1)) (realMaximum (wordLabel Prod.fst T z))
  let d := physicalLayout Prod.fst T ordinary_row_exact_two z j preserve
  let rwP : E ≃ Wires Pair H := rowWire (Pair:=Pair) Prod.fst ordinary_row_exact_two
  have hc : ∀ w : E, physicalCell (balancedMask (t+1) b) (d.seat w)=
      declaredCell (orientedNetwork d) (J7R13.rowFull z) (J7R13.colFull z) w := by
    intro w
    let e := rwP w
    have hf := (preserve e).trans (J7R13.actual_cell Prod.fst T z e)
    refine hf.trans ?_
    funext i
    change (J7R13.rowFull z (rowNode Prod.fst (rwP w)) i,
      J7R13.colFull z (colNode T (rwP w)) i) =
      (J7R13.rowFull z w.1 i, J7R13.colFull z (colOwner d w) i)
    exact Prod.ext
      (congrArg (fun v=>J7R13.rowFull z v i) (rowWire_owner Prod.fst ordinary_row_exact_two w))
      (congrArg (fun v=>J7R13.colFull z v i) (owner_layout Prod.fst T ordinary_row_exact_two z j preserve w).symm)
  have cap' : Nat.card (Page (t+1) b G)*2^(t+1)≤3*Nat.card E := by
    rwa [Nat.card_congr rwP] 
  refine ⟨b,⟨d,J7R13.rowFull z,J7R13.colFull z,hc,?_,?_,?_,?_,?_,?_,keep,hd,?_,?_⟩,?_⟩
  · rwa [← total_slots (balancedMask (K:=G) (t+1) b)]
  · rw [Nat.mul_comm]
    simpa only [Nat.card_eq_fintype_card] using cap'
  · intro i hi w
    have eq : i=(0:Fin (t+1)) := Fin.ext hi
    rw [eq]
    exact preserved_row_chart Prod.fst T ordinary_row_exact_two z j preserve hcap w
  · intro i hi w
    have eq : i=(0:Fin (t+1)) := Fin.ext hi
    rw [eq]
    exact preserved_col_chart Prod.fst T ordinary_row_exact_two z j preserve hcap w
  · exact relaxed_endpoint_of_raw Prod.fst T ordinary_row_exact_two z j preserve hnp hr
  · exact off_of_raw_label Prod.fst T ordinary_row_exact_two z j preserve cross
  · intro s x hx w hw
    change (j (rwP w)).2.val = _
    rw [hseat (rwP w) s x
      ((owner_layout Prod.fst T ordinary_row_exact_two z j preserve w).symm.trans hw) hx]
    rfl
  · intro s
    have hcard : Fintype.card E=Fintype.card (Wires Pair H) := Fintype.card_congr rwP
    dsimp only
    rw [hcard]
    exact hcount s
  · exact hcollision

theorem original_joint_geometry_at_printed_root
    (large : 2^(9*131072-1) < sourceSize N₀) :
    ∃ b, Nonempty (JointSourceGeometry ends (stepA (Nat.clog 2 (sourceSize N₀)) 0) b) := by
  obtain ⟨b,geom,_⟩ := original_joint_geometry_with_label_collision ends large
  exact ⟨b,⟨geom⟩⟩

#print axioms JointLabelCollision
#print axioms original_joint_geometry_with_label_collision
#print axioms original_joint_geometry_at_printed_root
end
end Paper6JointSeating




