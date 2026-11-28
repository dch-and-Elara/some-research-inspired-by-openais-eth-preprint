import J6R94ExteriorDebitGeometry
import J6R53OldOwnerRootBasis

/-! Exact eligibility and scope geometry of the original physical owner
roster. In particular a semantically free Gate still has physical ports;
the scope-plan (not the compiled Gate opcode) is the complete source. -/
namespace J6R112MeasuredRootLayoutStock
open scoped Classical Polynomial
open Std.Sat J6R15ModeCost J6R21Ancestor J6OrientedHost J6Mesh
open J6R10Repack J6R11Repack J6R21Leaf J6R27OriginalGate J6R24LegalLayout
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R35RootOrigins J6R53OldOwnerRoot
open J6R54ExteriorOwner J6R94ExteriorDebit

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4400
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V] {m n : ℕ}
variable (P : Plant V m n)
local notation "U" => (SourceVertex P)
local notation "W" => (constantRootWord m)

def ownerSide : U→Bool
  | .inl _ => false
  | .inr _ => true

def isPadding : U→Bool
  | .inl (.inr _) => true
  | .inr (.inr _) => true
  | _ => false

theorem side_matches_the_actual_owner (h : Port (RootWire m)) :
    ownerSide P (physicalSourceOwner P h)=side h := by
  cases h <;> rfl

theorem every_local_port_has_its_actual_side (u : U) (p : PlantPorts P W u) :
    side p.val=ownerSide P u := by
  have h : physicalSourceOwner P p.val=u := p.property
  exact (side_matches_the_actual_owner P p.val).symm.trans (congrArg (ownerSide P) h)

private theorem row_already_has_local_index
    (v : Left V W m (K m) (printedHalf m)) (j : oldScope P W v) :
    ∃ i : Fin (rootLocalGate P (.inl v)).degree,
      ((rootLocalGate P (.inl v)).port i).val=.inl (rowPort P W v j) := by
  rcases v with ⟨u,l⟩|⟨p,b⟩
  · exact ⟨j,rfl⟩
  · cases j
    exact ⟨⟨0,by change 0<1; decide⟩,rfl⟩

private theorem col_already_has_local_index
    (v : Right W m (K m) (printedHalf m) n) (b : Bool) :
    ∃ i : Fin (rootLocalGate P (.inr v)).degree,
      ((rootLocalGate P (.inr v)).port i).val=.inr (colPort P W v b) := by
  cases b
  · exact ⟨⟨0,by change 0<2; decide⟩,rfl⟩
  · exact ⟨⟨1,by change 1<2; decide⟩,rfl⟩

theorem original_local_scope_covers_each_physical_half (h : Port (RootWire m)) :
    ∃ i : Fin (rootLocalGate P (physicalSourceOwner P h)).degree,
      ((rootLocalGate P (physicalSourceOwner P h)).port i).val=h := by
  rcases h with e|e
  · let chart := rootRowChart (b:=K m) (l:=printedHalf m) P W
    let pair := chart.symm e
    have wire : rowPort P W pair.1 pair.2=e :=
      (rootRowChart_apply P W pair.1 pair.2).symm.trans (chart.apply_symm_apply e)
    obtain ⟨j, hj⟩ := row_already_has_local_index P pair.1 pair.2
    exact ⟨j,hj.trans (congrArg Sum.inl wire)⟩
  · let chart := rootColChart (b:=K m) (l:=printedHalf m) P W
    let pair := chart.symm e
    have wire : colPort P W pair.1 pair.2=e :=
      (rootColChart_apply P W pair.1 pair.2).symm.trans (chart.apply_symm_apply e)
    obtain ⟨j, hj⟩ := col_already_has_local_index P pair.1 pair.2
    exact ⟨j,hj.trans (congrArg Sum.inr wire)⟩


theorem root_free_padding_has_a_physical_scope_that_the_gate_discards
    (p : J6OrientedHost.Pad W m (K m) (printedHalf m)) :
    let u : U := .inl (.inr (p,true))
    (rootLocalGate P u).degree=1 ∧
      encodeGate (rootOperand P u ∘ (rootLocalGate P u).port) (rootLocalGate P u).gate=CodeGate.free := by
  exact ⟨rfl,rfl⟩

#print axioms side_matches_the_actual_owner
#print axioms every_local_port_has_its_actual_side
#print axioms original_local_scope_covers_each_physical_half
#print axioms root_free_padding_has_a_physical_scope_that_the_gate_discards
end
end J6R112MeasuredRootLayoutStock

