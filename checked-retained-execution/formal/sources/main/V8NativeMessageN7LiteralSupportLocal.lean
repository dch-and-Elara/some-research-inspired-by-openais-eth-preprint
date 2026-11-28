import V8NativeMessageN7PublicShift

/-! Exact Boolean-table sums on a real port whose possible values are
zero and the negative shift weight. These lemmas do not assume that a
list of local inputs comes from some other, independent packing. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

def shiftArg (c : ℚ) (b : Bool) : ℚ := if b then c else 0

def equality₂ (x y : ℚ) : ℚ := (1-x)*(1-y)+x*y
def equality₃ (x y z : ℚ) : ℚ := (1-x)*(1-y)*(1-z)+x*y*z
def clauseOr (x y : ℚ) : ℚ := x+y-x*y
def clauseImp (x y : ℚ) : ℚ := 1-x+x*y
def pinEval (x : ℚ) (sign : Bool) : ℚ := LiteralPortCompiler.affine sign x

theorem actual_binary_equality_eliminates (x y : ℚ) :
    (∑ b : Bool,∑ a : Bool,(if a=b then
      LiteralPortCompiler.affine b x * LiteralPortCompiler.affine a y else 0))=
      equality₂ x y := by
  simp [LiteralPortCompiler.affine,equality₂,add_comm]

theorem actual_equality₂_positive {x y : ℚ} (hx : x≤0) (hy : y≤0) :
    0<equality₂ x y := by
  have pp : 0<(1-x)*(1-y) := mul_pos (by linarith) (by linarith)
  have qq : 0≤x*y := mul_nonneg_of_nonpos_of_nonpos hx hy
  unfold equality₂
  linarith

theorem actual_equality₃_positive {x y z : ℚ} (hx : x≤0) (hy : y≤0) (hz : z≤0) :
    0<equality₃ x y z := by
  have a := mul_nonneg_of_nonpos_of_nonpos hx hy
  have b := mul_nonneg_of_nonpos_of_nonpos hx hz
  have c := mul_nonneg_of_nonpos_of_nonpos hy hz
  have form : equality₃ x y z = 1-x-y-z+x*y+x*z+y*z := by unfold equality₃; ring
  rw [form]
  linarith

theorem actual_implication_positive {x y : ℚ} (hx : x≤0) (hy : y≤0) :
    0<clauseImp x y := by
  have h := mul_nonneg_of_nonpos_of_nonpos hx hy
  unfold clauseImp
  linarith

theorem actual_or_shift_support {c : ℚ} (hc : c<0) (x y : Bool) :
    clauseOr (shiftArg c x) (shiftArg c y)≤0 ∧
    (clauseOr (shiftArg c x) (shiftArg c y)≠0 ↔ x=true ∨ y=true) := by
  have s := sq_nonneg c
  have h : 2*c-c*c<0 := by nlinarith
  cases x <;> cases y <;> simp [shiftArg,clauseOr,hc.ne,hc.le]
  exact ⟨by linarith,by linarith⟩

theorem actual_unary_shift_support {c : ℚ} (hc : c<0) (read : Bool) :
    pinEval (shiftArg c read) false > 0 ∧
    pinEval (shiftArg c read) true≤0 ∧
    (pinEval (shiftArg c read) true≠0 ↔ read=true) := by
  have h : 0<1-c := by linarith
  cases read <;> simp [shiftArg,pinEval,LiteralPortCompiler.affine,h,hc.ne,hc.le]

theorem actual_unit_gate_bounds (a b c : Bool) :
    |equality₂ (shiftArg (-1) a) (shiftArg (-1) b)|≤7 ∧
    |equality₃ (shiftArg (-1) a) (shiftArg (-1) b) (shiftArg (-1) c)|≤7 ∧
    |clauseOr (shiftArg (-1) a) (shiftArg (-1) b)|≤7 ∧
    |clauseImp (shiftArg (-1) a) (shiftArg (-1) b)|≤7 ∧
    ∀ s, |pinEval (shiftArg (-1) a) s|≤7 := by
  cases a <;> cases b <;> cases c <;> norm_num
    [shiftArg,equality₂,equality₃,clauseOr,clauseImp,pinEval,LiteralPortCompiler.affine]

end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.actual_binary_equality_eliminates
#print axioms V8NativeMessage.N7LiteralSupport.actual_equality₂_positive
#print axioms V8NativeMessage.N7LiteralSupport.actual_equality₃_positive
#print axioms V8NativeMessage.N7LiteralSupport.actual_implication_positive
#print axioms V8NativeMessage.N7LiteralSupport.actual_or_shift_support
#print axioms V8NativeMessage.N7LiteralSupport.actual_unary_shift_support
#print axioms V8NativeMessage.N7LiteralSupport.actual_unit_gate_bounds
