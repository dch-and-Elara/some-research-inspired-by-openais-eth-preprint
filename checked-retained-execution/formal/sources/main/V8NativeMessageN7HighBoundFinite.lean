import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-! Height after elimination of the real row bits at the unit shift.
The column cube is full (including unshifted columns), not a matching
or a short subset of assignments. -/
namespace V8NativeMessage.N7HighBound
open scoped Classical BigOperators

noncomputable section

variable {E V : Type*} [Fintype E]

def columnContraction (rows : Finset V) (keep : (E→Bool)→Bool)
    (r : V→(E→Bool)→ℤ) : ℤ :=
  ∑ y : E→Bool, if keep y then ∏ v∈rows,r v y else 0

theorem actual_column_height
    (rows : Finset V) (keep : (E→Bool)→Bool) (r : V→(E→Bool)→ℤ)
    (hRows : rows.card≤Fintype.card E) (hRow : ∀ y v, v∈rows → |r v y|≤7) :
    |columnContraction rows keep r| ≤ (2:ℤ)^Fintype.card E * 7^Fintype.card E := by
  let M := Fintype.card E
  let b := (7:ℤ)^M
  let x (y : E→Bool) : ℤ := if keep y then ∏ v∈rows,r v y else 0
  have hTerm (y : E→Bool) : |x y|≤b := by
    unfold x
    split
    · rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _v∈rows,(7:ℤ) := Finset.prod_le_prod
          (fun _ _=>abs_nonneg _) (fun v hv=>hRow y v hv)
        _ = (7:ℤ)^rows.card := Finset.prod_const _
        _ ≤ b := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤7) hRows
    · simp only [abs_zero]
      positivity
  change |∑ y : E→Bool,x y|≤(2:ℤ)^M*b
  calc
    _ ≤ ∑ y : E→Bool,|x y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y : E→Bool,b := Finset.sum_le_sum (fun y _=>hTerm y)
    _ = _ := by simp [M]

theorem unit_height_strict {M : ℕ} (hM : 0<M) :
    (2:ℤ)^M*7^M < (2:ℤ)^(4*M) := by
  rw [←mul_pow,pow_mul]
  change (14:ℤ)^M < (16:ℤ)^M
  exact pow_lt_pow_left₀ (by norm_num) (by norm_num) hM.ne'

theorem unit_centered_window {M p : ℕ} (hM : 0<M) (hp : 4*M<p)
    {z : ℤ} (hb : |z|≤(2:ℤ)^M*7^M) : 2*|z|<(2:ℤ)^p := by
  have h := mul_lt_mul_of_pos_left (hb.trans_lt (unit_height_strict hM)) (by norm_num : (0:ℤ)<2)
  calc
    _ < 2*(2:ℤ)^(4*M) := h
    _ = (2:ℤ)^(4*M+1) := (pow_succ' _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (by omega)

theorem unit_column_window
    (rows : Finset V) (keep : (E→Bool)→Bool) (r : V→(E→Bool)→ℤ)
    (hRows : rows.card≤Fintype.card E) (hRow : ∀ y v, v∈rows → |r v y|≤7)
    (hM : 0<Fintype.card E) {p : ℕ} (hp : 4*Fintype.card E<p) :
    2*|columnContraction rows keep r| < (2:ℤ)^p :=
  unit_centered_window hM hp (actual_column_height rows keep r hRows hRow)

#print axioms actual_column_height
#print axioms unit_height_strict
#print axioms unit_centered_window
#print axioms unit_column_window
end
end V8NativeMessage.N7HighBound
