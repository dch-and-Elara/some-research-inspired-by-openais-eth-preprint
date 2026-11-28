import J4R43LiteralOutsideTiedChart
import J4R43LiteralOutsideCensus
import J4R43LiteralOutsideHamming

/-! The four-clone graph's original frozen label construction (including
its exterior-pair tied coordinate) has the required band loads on the
actual large source regime. This is the original graph with transposition,
not a replacement by an abstract constant-degree tensor. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J1MainSourceCollision J6ActiveRun J6R12Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6800000
set_option maxRecDepth 2500

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E₀ : Finset (V×V)) (cub : ∀ v,GraphCutMoments.degree E₀ v=3)
variable (loops : ∀ v,(v,v)∉E₀)
local notation "F" => replacedEdges E₀ cub
local notation "reg" => replaced_cubic E₀ cub loops
local notation "N" => dNetwork F reg
variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0

theorem actual_swapped_cell_count (a : ℕ) :
    Nat.card (Cell (Fin a) (Fin 64))=J9PrintedSchedule.arrayCard a := by
  simp only [total_cells,Fintype.card_fin,J9PrintedSchedule.arrayCard]

theorem actual_mesh_le_cells (a : ℕ) : 2^a≤J9PrintedSchedule.arrayCard a := by
  unfold J9PrintedSchedule.arrayCard
  exact (Nat.pow_le_pow_left (by norm_num : 2≤64) a).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem original_four_clone_has_one_fixed_band (d : ColumnReady F reg (f:=f))
    (tied : Fin a₀) (target : TriVertex V)
    (width : 8*reciprocal 3≤2^a₀)
    (enough : 1638400*(J9PrintedSchedule.arrayCard a₀)^2≤Nat.card (DWire F)) :
    ∃ z : DPrimitives E₀ cub a₀→Fin 64,
      ∃ Q : ColumnPacking F reg (f:=f),
        (∀ p : TriVertex V,Q.colLabel (.inr (.inl p)) tied=
          z (.inr (.inr ((exteriorPort E₀ cub).symm p).1))) ∧
        BandCertificate Q (printedBand a₀ 3) ∧
        (Q.seat (literalPin F target)).2.val+1=2^a₀ := by
  let M := Nat.card (DWire F)
  let D := J9PrintedSchedule.arrayCard a₀
  let L := (2:ℕ)^a₀
  have dpos : 0<D := by unfold D J9PrintedSchedule.arrayCard; positivity
  have col : 2*D^2*3≤M := by
    calc
      _ = 6*D^2 := by ring
      _ ≤ 1638400*D^2 := Nat.mul_le_mul_right _ (by decide)
      _ ≤ _ := enough
  have slots : L*D≤M := by
    have s := d.paddedSlots
    change L*D≤Fintype.card (DWire F) at s
    change L*D≤Nat.card (DWire F)
    rw [Nat.card_eq_fintype_card]
    exact s
  obtain ⟨z,P,ties,round,variance⟩ := d_actual_tied_packing E₀ cub loops tied 3 le_rfl col slots
  have var : varianceScore (declaredCell N P.rowLabel P.colLabel)≤6*(M:ℚ) := by
    convert variance using 1; ring
  have L_le_D : L≤D := actual_mesh_le_cells a₀
  have rough : 384*D^2≤M := (Nat.mul_le_mul_right _ (by decide : 384≤1638400)).trans enough
  have mesh : 8*L*D≤M := by
    calc
      _ ≤ 8*D*D := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ L_le_D)
      _ = 8*D^2 := by ring
      _ ≤ _ := (Nat.mul_le_mul_right _ (by decide : 8≤1638400)).trans enough
  have small : 4*starWidth 3*D≤M := by
    have Dpow : D≤D^2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ dpos
    calc
      _ ≤ (4*starWidth 3)*D^2 := Nat.mul_le_mul_left _ Dpow
      _ ≤ 1638400*D^2 := Nat.mul_le_mul_right _ (by decide)
      _ ≤ _ := enough
  have large : 64*(reciprocal 3)^2*(starWidth 3)^2*D^2≤M := by
    convert enough using 1
  have ready := actual_census_from_variance P 3 round var
    (by simpa only [nCells,actual_swapped_cell_count] using rough)
    (by simpa only [nCells,actual_swapped_cell_count] using mesh)
    (by simpa only [nCells,actual_swapped_cell_count] using small)
    (by simpa only [nCells,actual_swapped_cell_count] using large)
  have hr (v : DOld F) : Nat.card {e : DWire F//(dNetwork F reg).row e=v}≤3 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    convert d_old_degree F reg v using 1; congr 1; ext e; simp [facFibre]
  have hc (v : MainClonedCNF.Port F) : Nat.card {e : DWire F//(dNetwork F reg).col e=v}≤3 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    have b := (d_subdivision_degree F reg v).le.trans (by decide : 2≤3)
    convert b using 1; congr 1; ext e; simp [varFibre]
  obtain ⟨supply⟩ := same_post_transpose_quota P 3 (literalPin F target) ready.1 hr hc ready.2.1 ready.2.2
  have h := printed_band_legal a₀ 3 width
  obtain ⟨Q,_,columns,_,_,band,last⟩ :=
    realize_band_with_pin (transposePacking P) (printedBand a₀ 3) h.1 h.2 (literalPin F target) supply
  refine ⟨z,Q,?_,band,last⟩
  intro v
  rw [columns]
  exact ties v

#print axioms actual_swapped_cell_count
#print axioms actual_mesh_le_cells
#print axioms original_four_clone_has_one_fixed_band
end
end J4R43LiteralOutside

