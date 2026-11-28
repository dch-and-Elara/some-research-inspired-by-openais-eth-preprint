import LayerRecovery
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! The exact J6 dyadic mesh. All exponents use the paper's fixed
epsilon = 1/131072. The guards and address counts are integer inequalities. -/
namespace J6Mesh
def b (m : ℕ) := Nat.clog 2 (m+2)
def lambda (m : ℕ) := 524288*b m
def u (m : ℕ) := 4*b m
def a (m : ℕ) := 8*b m
def L (m : ℕ) := 2^a m
def D (m : ℕ) := 2^(96*b m)
def K (m : ℕ) := 2^(524184*b m)
def M (m : ℕ) := 2^lambda m

theorem b_pos (m : ℕ) : 0 < b m := by
  apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).mpr
  simp
  omega

theorem dyadic_rounding (m : ℕ) : m+2 ≤ 2^b m ∧ 2^b m < 2*(m+2) := by
  have hp : 2^(b m-1) < m+2 := Nat.pow_pred_clog_lt_self (by decide) (by omega)
  have ht : b m-1+1 = b m := Nat.sub_add_cancel (b_pos m)
  refine ⟨Nat.le_pow_clog (by decide) _,?_⟩
  calc
    _ = 2^(b m-1)*2 := by rw [← pow_succ,ht]
    _ < (m+2)*2 := Nat.mul_lt_mul_of_pos_right hp (by decide)
    _ = _ := by ring

theorem mesh_product (m : ℕ) : D m * (K m * L m) = M m := by
  unfold D K L M lambda a
  rw [← pow_add,← pow_add]
  congr 1
  omega

theorem cell_palette (m : ℕ) : (64:ℕ)^(2*a m) = D m := by
  calc
    _ = (2^6)^(2*a m) := by norm_num
    _ = _ := by rw [← pow_mul]; unfold a D; congr 1; omega

set_option exponentiation.threshold 524288 in
theorem size_powers (m : ℕ) :
    (m+2)^8 ≤ L m ∧ L m ≤ (2*(m+2))^8 ∧
      M m ≤ (2*(m+2))^524288 := by
  have ⟨hlo,hhi⟩ := dyadic_rounding m
  have hL : L m = (2^b m)^8 := by rw [L,a,Nat.mul_comm 8,pow_mul]
  have hM : M m = (2^b m)^524288 := by rw [M,lambda,Nat.mul_comm 524288,pow_mul]
  rw [hL,hM]
  exact ⟨Nat.pow_le_pow_left hlo _,Nat.pow_le_pow_left hhi.le _,Nat.pow_le_pow_left hhi.le _⟩

theorem mesh_seats (m : ℕ) : 2*m+1 < L m ∧ 4*(m+2) ≤ K m ∧ Even (L m) := by
  have hb := b_pos m
  have hlo := (dyadic_rounding m).1
  have hL : (2:ℕ)*2^b m ≤ L m := by
    rw [L,a,mul_comm,← pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hK : (2:ℕ)^b m * 4 ≤ K m := by
    rw [K,show (4:ℕ)=2^2 by decide,← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hE : a m - 1 + 1 = a m := by unfold a; omega
  refine ⟨by omega, by omega,?_⟩
  refine ⟨2^(a m-1),?_⟩
  unfold L
  calc
    2^a m = 2^(a m-1+1) := congrArg (fun n : ℕ => 2^n) hE.symm
    _ = 2^(a m-1)+2^(a m-1) := by rw [pow_succ,Nat.mul_two]

def physicalSize (m native : ℕ) := M m - L m*m + L m*native

/-- Padding the actual physical copies leaves the input in exactly
the claimed source ceiling-log interval, not merely O(M). -/
theorem physicalSize_ceiling (m native : ℕ) (hs : native ≤ m) :
    2^(lambda m-1) < physicalSize m native ∧ physicalSize m native ≤ M m ∧
      Nat.clog 2 (physicalSize m native) = lambda m := by
  have hL : 0 < L m := by unfold L; positivity
  have hD : 0 < D m := by unfold D; positivity
  have hLambda : 0 < lambda m := by unfold lambda; have := b_pos m; omega
  have hK := (mesh_seats m).2.1
  have hM : K m * L m ≤ M m := by
    rw [← mesh_product]
    exact Nat.le_mul_of_pos_left _ hD
  have hb : L m*m*2 < M m := by
    apply lt_of_lt_of_le _ hM
    have hh := Nat.mul_lt_mul_of_pos_right (show m*2 < K m by omega) hL
    nlinarith
  have he : lambda m-1+1 = lambda m := Nat.sub_add_cancel hLambda
  have hp : 2^(lambda m-1)*2 = M m := by rw [← pow_succ,he,M]
  have hn : L m*native ≤ L m*m := Nat.mul_le_mul_left _ hs
  have hl : 2^(lambda m-1) < physicalSize m native := by
    unfold physicalSize
    omega
  have hu : physicalSize m native ≤ M m := by
    unfold physicalSize
    omega
  refine ⟨hl,hu,?_⟩
  apply le_antisymm
  · exact (Nat.clog_le_iff_le_pow (by decide)).mpr hu
  · have h := (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).mpr hl
    omega

def index (m : ℕ) (i : Fin (m+1)) : ℕ := 2*i.val+1

theorem address_index (m : ℕ) (i : Fin (m+1)) :
    0 < index m i ∧ Odd (index m i) ∧ index m i ≤ 2*m+1 ∧ index m i < L m := by
  have hb := (mesh_seats m).1
  have hi := i.isLt
  unfold index
  exact ⟨by omega,⟨i.val,rfl⟩,by omega,by omega⟩

noncomputable def point (m : ℕ) (i : Fin (m+1)) : ℚ :=
  -LayerRecovery.gridRatio (L m) (index m i)

theorem negative_distinct_points (m : ℕ) :
    (∀ i, point m i < 0) ∧ Function.Injective (point m) := by
  refine ⟨fun i => neg_neg_of_pos (LayerRecovery.gridRatio_pos (address_index m i).2.2.2),?_⟩
  intro i j h
  have h' := LayerRecovery.negative_mesh_injective (L m)
    (show index m i ∈ {t | t < L m} from (address_index m i).2.2.2)
    (show index m j ∈ {t | t < L m} from (address_index m j).2.2.2) h
  apply Fin.ext
  unfold index at h'
  omega

def fallbackAddresses (m : ℕ) := (m+1)*(M m*(2*L m-1)+1)

/-- Upper bound on the number of probes if the designated binary grid
does not contain zero. With zero available it is exactly m+1. -/
theorem fallbackAddresses_polynomial (m : ℕ) :
    fallbackAddresses m ≤ (m+1)*(2*(2*(m+2))^(524288+8)+1) := by
  obtain ⟨_,hL,hM⟩ := size_powers m
  unfold fallbackAddresses
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  calc
    _ ≤ M m*(2*L m) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤ (2*(m+2))^524288*(2*(2*(m+2))^8) :=
      Nat.mul_le_mul hM (Nat.mul_le_mul_left _ hL)
    _ = _ := by rw [pow_add, mul_left_comm]

#print axioms mesh_product
#print axioms cell_palette
#print axioms size_powers
#print axioms mesh_seats
#print axioms physicalSize_ceiling
#print axioms address_index
#print axioms negative_distinct_points
#print axioms fallbackAddresses_polynomial
end J6Mesh
