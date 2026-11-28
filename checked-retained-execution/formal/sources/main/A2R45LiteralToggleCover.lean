
import A2R45LiteralToggle

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3750000
set_option maxRecDepth 1650
set_option linter.unusedSectionVars false

/-! There is exactly one actual physical truth-table argument affected,
not merely one address after a possibly many-to-one readout. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open FixedHostAcquisition J6R10Repack AAcquisitionCost
open A1R43Literal.General

noncomputable section
variable {n : ℕ} {Pad : Type}
local notation "N" => nativeNetwork n Pad

theorem all_real_row_ports_on_odd_wire (r : Row n) :
    Function.Surjective (fun j : WireAt r=>rowsOdd (Pad:=Pad) r (actualSimRowPort r j)) := by
  rintro ⟨(⟨⟨r',j⟩,b⟩|p)|q,h⟩
  · cases b
    · cases h
    · have hr : r'=r := Sum.inl.inj (Sum.inl.inj h)
      subst r'
      exact ⟨j,rfl⟩
  · cases h
  · cases h

theorem physical_pair_read_injective (q : Pair n) :
    Function.Injective (@nativePairRead n Pad q) := by
  intro x y h
  funext i
  obtain ⟨j,hj⟩ := all_real_row_ports_on_odd_wire (Pad:=Pad) (.inl q) i
  change rowsOdd (Pad:=Pad) (.inl q) (actualSimRowPort (.inl q) j)=i at hj
  have e := congrFun h j
  change x (rowsOdd (.inl q) (actualSimRowPort (.inl q) j)) =
    y (rowsOdd (.inl q) (actualSimRowPort (.inl q) j)) at e
  rwa [hj] at e

theorem only_one_full_table_argument_changes (enabled : Pair n→Bool) (q : Pair n)
    (x : ParentPorts N (pairVertex (Pad:=Pad) q)→Bool) :
    tableFlag (Input.encode (setSwitch enabled q false)) (pairVertex q) x ≠
      tableFlag (Input.encode (setSwitch enabled q true)) (pairVertex q) x ↔
      x=(fun _=>true) := by
  rw [actual_toggled_pair_cell]
  constructor
  · rintro ⟨_,h⟩
    apply physical_pair_read_injective q
    funext b
    let y := nativePairRead q x
    change (pairBitAddress y).val=3 at h
    change y b=true
    have hv : (if y false then 2 else 0)+(if y true then 1 else 0)=3 := h
    cases b <;> cases ha : y false <;> cases hb : y true <;> simp_all
  · intro h
    rw [h]
    exact ⟨rfl,rfl⟩

#print axioms all_real_row_ports_on_odd_wire
#print axioms physical_pair_read_injective
#print axioms only_one_full_table_argument_changes
end
end A2R45Literal
