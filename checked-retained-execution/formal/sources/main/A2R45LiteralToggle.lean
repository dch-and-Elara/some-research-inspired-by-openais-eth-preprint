
import A2R45LiteralGate

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13000000
set_option maxRecDepth 1750
set_option linter.unusedSectionVars false

/-! Changing an input graph bit changes exactly one actual old-row
truth-table address. All auxiliary, equality, pin and filler files have
identical local words and creation tags. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial FixedHostAcquisition J6R10Repack J6R9Recursive AAcquisitionCost

noncomputable section
variable {n : ℕ} {Pad : Type}
local notation "N" => nativeNetwork n Pad

def pairVertex (q : Pair n) : NativeRow n Pad⊕NativeCol n Pad :=
  .inl (.inl (.inl q))

def nativePairRead (q : Pair n) (x : ParentPorts N (pairVertex (Pad:=Pad) q)→Bool) :
    Bool→Bool :=
  x ∘ rowsOdd (.inl q) ∘ actualSimRowPort (.inl q)

theorem native_pair_table_reads_tape (w : Input n) (q : Pair n)
    (x : ParentPorts N (pairVertex (Pad:=Pad) q)→Bool) :
    tableFlag w (pairVertex q) x=serializedRead w (.inl q) (nativePairRead q x) := rfl

theorem actual_toggled_pair_cell (enabled : Pair n→Bool) (p q : Pair n)
    (x : ParentPorts N (pairVertex (Pad:=Pad) q)→Bool) :
    tableFlag (Input.encode (setSwitch enabled p false)) (pairVertex q) x ≠
      tableFlag (Input.encode (setSwitch enabled p true)) (pairVertex q) x ↔
      q=p ∧ (pairBitAddress (nativePairRead q x)).val=3 := by
  rw [native_pair_table_reads_tape,native_pair_table_reads_tape]
  exact switched_row_changes_exact_cell enabled p q (nativePairRead q x)

theorem all_nonpair_words_fixed (w w' : Input n) (v : NativeRow n Pad⊕NativeCol n Pad)
    (nv : ∀ q : Pair n,v≠pairVertex q) (x : ParentPorts N v→Bool) :
    tableFlag w v x=tableFlag w' v x := by
  rcases v with (r|z)|c
  · cases r with
    | inl q => exact (nv q rfl).elim
    | inr l =>
      change serializedRead w (.inr l) _ = serializedRead w' (.inr l) _
      exact copy_tape_unchanged w w' l _
  · rfl
  · cases c <;> rfl

#print axioms native_pair_table_reads_tape
#print axioms actual_toggled_pair_cell
#print axioms all_nonpair_words_fixed
end
end A2R45Literal
