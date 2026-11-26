import P5MainIteratorPaid
import P5MainIteratorScopes

/-! Exact native formula bridges: integer Taylor floor, actual copied
row count, and the printed measurement budget once its tail is certified. -/
namespace P5MainIterator
open scoped BigOperators Classical

theorem real_floor_ratio_nat (a q : ℕ) : ⌊(a:ℝ)/(q:ℝ)⌋₊ = a/q := by
  by_cases he : q=0
  · simp [he]
  have hq := Nat.pos_of_ne_zero he
  have hqr : 0<(q:ℝ) := by exact_mod_cast hq
  have H := Nat.mod_add_div a q
  rw [Nat.mul_comm q (a/q)] at H
  have HT := Nat.mod_lt a hq
  apply (Nat.floor_eq_iff (by positivity : 0≤(a:ℝ)/(q:ℝ))).mpr
  constructor
  · apply (le_div_iff₀ hqr).mpr
    exact_mod_cast (by omega : (a/q)*q≤a)
  · apply (div_lt_iff₀ hqr).mpr
    exact_mod_cast (by rw [Nat.add_mul,one_mul]; omega : a < (a/q+1)*q)

theorem printed_nominal_real_floors (n R Q k mTest l : ℕ)
    (hk : 1≤k) (hl : n≤l-1) :
    ⌊(1:ℝ)*(n:ℝ)*(R:ℝ)/(Q:ℝ)⌋₊ ≤ (3*n*R)/Q ∧
    ⌊(1:ℝ)*(n:ℝ)*(R:ℝ)/(Q:ℝ)⌋₊ ≤ k*(mTest+2*(l-1))*R/Q := by
  rw [one_mul,←Nat.cast_mul,real_floor_ratio_nat]
  exact printed_nominal_orders n R Q k mTest l hk hl

variable {Copy I B : Type*} [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

omit [Fintype Copy] [Fintype B] in
def copied_row_equiv (keep : ℕ→Prop) :
    Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep ≃
      Copy × Exceptional (Unequal (I:=I) (B:=B)) keep where
  toFun := fun ⟨⟨⟨c,o⟩,w⟩,h⟩ => ⟨c,⟨⟨o,w⟩,h⟩⟩
  invFun := fun ⟨c,⟨⟨o,w⟩,h⟩⟩ => ⟨⟨⟨c,o⟩,w⟩,h⟩
  left_inv := by rintro ⟨⟨⟨_,_⟩,_⟩,_⟩; rfl
  right_inv := by rintro ⟨_,⟨⟨_,_⟩,_⟩⟩; rfl

theorem literal_copied_rows (keep : ℕ→Prop) :
    Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep) =
      Fintype.card Copy * Fintype.card (Exceptional (Unequal (I:=I) (B:=B)) keep) := by
  rw [Fintype.card_congr (copied_row_equiv keep),Fintype.card_prod]

theorem printed_row_budget (r H D cB M n b : ℕ) (δ τ : ℝ)
    (hd : 0≤δ) (hr : 0<r) (hb : 0<b)
    (hcopies : H*D≤2*M) (hsize : M≤b*n)
    (hrows : (cB:ℝ)≤δ*(D:ℝ)) (hδ : δ≤τ/((r:ℝ)*(b:ℝ))) :
    (r:ℝ)*((H:ℝ)*(cB:ℝ))≤2*τ*(n:ℝ) := by
  have hr' : 0<(r:ℝ) := by exact_mod_cast hr
  have hb' : 0<(b:ℝ) := by exact_mod_cast hb
  have hcopy : (H:ℝ)*(D:ℝ)≤2*(M:ℝ) := by exact_mod_cast hcopies
  have hM : (M:ℝ)≤(b:ℝ)*(n:ℝ) := by exact_mod_cast hsize
  have hmid : (r:ℝ)*((b:ℝ)*δ)≤τ := by
    have h := (le_div_iff₀ (mul_pos hr' hb')).mp hδ
    linarith only [h]
  calc
    _ ≤ (r:ℝ)*((H:ℝ)*(δ*(D:ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrows (by positivity)) hr'.le
    _ = ((r:ℝ)*δ)*((H:ℝ)*(D:ℝ)) := by ring
    _ ≤ ((r:ℝ)*δ)*(2*(M:ℝ)) := mul_le_mul_of_nonneg_left hcopy (by positivity)
    _ ≤ ((r:ℝ)*δ)*(2*((b:ℝ)*(n:ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM (by norm_num)) (by positivity)
    _ = ((r:ℝ)*((b:ℝ)*δ))*(2*(n:ℝ)) := by ring
    _ ≤ τ*(2*(n:ℝ)) := mul_le_mul_of_nonneg_right hmid (by positivity)
    _ = _ := by ring

#print axioms real_floor_ratio_nat
#print axioms printed_nominal_real_floors
#print axioms copied_row_equiv
#print axioms literal_copied_rows
#print axioms printed_row_budget
end P5MainIterator
