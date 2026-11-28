import V8NativeMessageN7LiteralSupportZero
import V8NativeMessageN7LiteralSupportBlock
import V8NativeMessageN7LiteralSupportComponent
import V8NativeMessageN7Shift

/-! Exact characteristic-two factorization by any partition that does
not cut an actual shifted wire.  Physical packet groups are not used
as a proxy for these components. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles DenominatorBudget
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000
set_option maxRecDepth 2100
noncomputable section

variable {E A B G K R : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] [Fintype K] [CommRing R]
variable {a : ℕ} {N : Network E A B} (P : PhysicalPacking N a G)

def literalComponentFactors (t : ℤ) (color : A⊕B→K)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) (k : K) : R :=
  localSum (fun q=>color (.inr (N.col q))) color false
    (fun v y=>bit R (flags v (componentWord P t v y))) k

theorem factor_actual_unit_wiring (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (color : A⊕B→K)
    (uncut : ∀ {r q},Matches P t r q→color (.inl (N.row r))=color (.inr (N.col q)))
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) :
    signedRoot P i t (1:R) flags=∏ k,literalComponentFactors P t color flags k := by
  rw [literal_signed_cube_is_residue_slot P i ht hv,
      partial_wiring_sums_exactly_one_row_word]
  have flagsOp (y : E→Bool) :
      bit R (rowKeep N flags (fun r=>readTrueShift P t r y) && colKeep N flags y)=
        ∏ v,bit R (flags v (componentWord P t v y)) :=
    (actual_flags_on_full_side_words (R:=R) flags (fun r=>readTrueShift P t r y) y).symm
  simp only [flagsOp]
  apply split_actual_bits
  intro v y y' same
  congr 2
  apply actual_rewired_vertex_depends_only_inside_component P
  intro q h
  apply same
  exact (any_valid_component_class_preserved P t color uncut h).symm

theorem factor_actual_parity_wiring (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (mem : t∈P1DyadicGrid.grid a) (φ : TwoLocal→+*R) (h2 : (2:R)=0)
    (color : A⊕B→K)
    (uncut : ∀ {r q},Matches P t r q→color (.inl (N.row r))=color (.inr (N.col q)))
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) :
    φ (exactZero P i t flags)=∏ k,literalComponentFactors P t color flags k := by
  rw [exactZero,full_signed_root_is_zero_polynomial,map_signed_root,
      V8NativeMessage.N7.rho_mod_two φ h2 mem]
  exact factor_actual_unit_wiring P i ht hv color uncut flags

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.factor_actual_unit_wiring
#print axioms V8NativeMessage.N7LiteralSupport.factor_actual_parity_wiring
