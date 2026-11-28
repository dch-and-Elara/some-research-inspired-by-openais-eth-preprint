import V8NativeMessageN7HighBoundInteger
import V8NativeMessageN7HighBoundFinite
import V8NativeMessageN7HighBoundReceipt

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14500000
set_option maxRecDepth 2100

/-! The height receipt is supplied by row elimination of the same
integer source contraction certified in HighBoundInteger. -/
namespace V8NativeMessage.N7HighBound
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
  V8NativeMessage.N7LiteralSupport

noncomputable section

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a)
variable (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)

variable {f : ℤ[X]}

theorem unit_received_after_eliminating_rows
    {V : Type*} (rows : Finset V) (keep : (E→Bool)→Bool) (r : V→(E→Bool)→ℤ)
    (shape : unitInteger P i flags=columnContraction rows keep r)
    (hRows : rows.card≤Fintype.card E) (hRow : ∀ y v, v∈rows → |r v y|≤7)
    (hM : 0<Fintype.card E) (p : ℕ) (hp : 4*Fintype.card E<p)
    (hf : f.Monic) (hd : 0<f.natDegree) :
    let v := (unitInteger P i flags:Box f 1 p)
    |unitInteger P i flags| ≤ (2:ℤ)^Fintype.card E*7^Fintype.card E ∧
    centeredBox p f hf v=unitInteger P i flags ∧
    (v=0 ↔ exactZero P i (-1) flags=0) := by
  let Z := unitInteger P i flags
  have bound : |Z|≤(2:ℤ)^Fintype.card E*7^Fintype.card E := by
    change |unitInteger P i flags|≤_
    rw [shape]
    exact actual_column_height rows keep r hRows hRow
  have hFit : 2*|Z|<(2:ℤ)^p := unit_centered_window hM hp bound
  have small : |Z|<(2:ℤ)^p := by linarith only [hFit,abs_nonneg Z]
  have pos : 0<p := by omega
  refine ⟨bound,centered_box_recovers p pos f hf hd Z hFit,?_⟩
  exact (integer_box_zero_iff_of_height p pos f hf hd Z small).trans
    (exact_unit_zero_iff P i flags).symm

theorem original_unit_zero_probe_centered
    (hv : padicValInt 2 (-1)=i.val) (p₀ p : ℕ) (hp₀ : 0<p₀)
    (hf : f.Monic) (hd : 0<f.natDegree)
    {V : Type*} (rows : Finset V) (keep : (E→Bool)→Bool) (r : V→(E→Bool)→ℤ)
    (shape : unitInteger P i flags=columnContraction rows keep r)
    (hRows : rows.card≤Fintype.card E) (hRow : ∀ y v, v∈rows → |r v y|≤7)
    (hM : 0<Fintype.card E) (hp : 4*Fintype.card E<p) :
    let v := nativeUnitZeroSlot P i flags hv p₀ p hf
    |unitInteger P i flags| ≤ (2:ℤ)^Fintype.card E*7^Fintype.card E ∧
    centeredBox p f hf v=unitInteger P i flags ∧
    (v=0 ↔ exactZero P i (-1) flags=0) := by
  dsimp only
  rw [actual_unit_slot_is_integer P i flags hv p₀ p hp₀ hf hd]
  exact unit_received_after_eliminating_rows P i flags rows keep r shape hRows hRow hM p hp hf hd

#print axioms unit_received_after_eliminating_rows
#print axioms original_unit_zero_probe_centered
end
end V8NativeMessage.N7HighBound
