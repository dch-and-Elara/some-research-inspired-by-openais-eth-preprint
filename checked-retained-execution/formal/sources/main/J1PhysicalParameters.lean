import Mathlib.Tactic
import Mathlib.Data.Nat.Log

/-! A fully numeric transfer from the published dyadic constraints
to the finite physical J1 existence guard and both source load guards.
The logarithmic ceiling details are confined to the dyadic premise. -/
namespace J1PhysicalParameters

private theorem poly_pow_aux (u : ℕ) :
    16384 * (32+u+1)^2 ≤ 2^(32+u) := by
  induction u with
  | zero => norm_num
  | succ u ih =>
      have h : (32+u+1+1)^2 ≤ 2*(32+u+1)^2 := by
        nlinarith [show 2 ≤ 32+u by omega]
      calc
        16384 * (32+u.succ+1)^2 =
            16384 * (32+u+1+1)^2 := by rw [Nat.succ_eq_add_one]; ring
        _ ≤ 16384 * (2*(32+u+1)^2) := Nat.mul_le_mul_left _ h
        _ = 2*(16384*(32+u+1)^2) := by ring
        _ ≤ 2*(2^(32+u)) := Nat.mul_le_mul_left _ ih
        _ = 2^(32+u.succ) := by rw [Nat.add_succ,pow_succ,Nat.mul_comm]

private theorem poly_pow (m : ℕ) (hm : 32 ≤ m) :
    16384 * (m+1)^2 ≤ 2^m := by
  have h := poly_pow_aux (m-32)
  rwa [Nat.add_sub_of_le hm] at h

theorem dyadic_guards (N Q r L : ℕ)
    (hL : 256 ≤ L) (hLower : 2^L ≤ 8*N)
    (hQ : Q ≤ L) (hr : r^2 ≤ L) (hrPos : 0 < r)
    (hPacking : (r^Q)^256 ≤ 2^L) :
    192*Q*r^2*r^Q+6 < N ∧
      10*(r^(2*Q))^2 ≤ 12*N ∧ 2*Q*r^2 ≤ 4*N := by
  let m := L/8
  let K := r^Q
  have hm : 32 ≤ m := by dsimp [m]; omega
  have hLt : L ≤ 8*(m+1) := by dsimp [m]; omega
  have hKpos : 0 < K := pow_pos hrPos _
  have hkPow : K^256 ≤ (2^m)^256 := by
    calc
      _ ≤ 2^L := hPacking
      _ ≤ 2^(m*256) := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
        (show L ≤ m*256 by dsimp [m]; omega)
      _ = _ := by rw [pow_mul]
  have hK : K ≤ 2^m :=
    (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide)).mp hkPow
  have hc : 192*Q*r^2 < 2^m := by
    calc
      _ ≤ 192*L*L := Nat.mul_le_mul (Nat.mul_le_mul_left _ hQ) hr
      _ ≤ 192*(8*(m+1))*(8*(m+1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hLt) hLt
      _ = 12288*(m+1)^2 := by ring
      _ < 16384*(m+1)^2 := Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)
      _ ≤ _ := poly_pow m hm
  have hMain : 192*Q*r^2*K < 2^(2*m) := by
    calc
      _ < 2^m*K := Nat.mul_lt_mul_of_pos_right hc hKpos
      _ ≤ 2^m * 2^m := Nat.mul_le_mul_left _ hK
      _ = _ := by rw [two_mul,pow_add]
  have hMainScale : 2^(2*m+4) ≤ 8*N :=
    (Nat.pow_le_pow_right (by decide) (show 2*m+4 ≤ L by dsimp [m]; omega)).trans hLower
  have hSmall : 8 ≤ 2^(2*m) := by
    change 2^3 ≤ 2^(2*m)
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 3 ≤ 2*m)
  have hMainGuard : 192*Q*r^2*K+6 < N := by
    rw [pow_add] at hMainScale
    norm_num at hMainScale
    omega
  have hCellScale : 2^(4*m+3) ≤ 8*N :=
    (Nat.pow_le_pow_right (by decide) (show 4*m+3 ≤ L by dsimp [m]; omega)).trans hLower
  have hCell : (r^(2*Q))^2 ≤ N := by
    calc
      _ = K^4 := by dsimp [K]; rw [← pow_mul,← pow_mul]; congr 1; ring
      _ ≤ (2^m)^4 := Nat.pow_le_pow_left hK _
      _ = 2^(4*m) := by rw [← pow_mul,Nat.mul_comm m]
      _ ≤ N := by rw [pow_add] at hCellScale; norm_num at hCellScale; omega
  have hGroup : Q*r^2 ≤ 192*Q*r^2*K := by
    calc
      _ = 1*(Q*r^2)*1 := by simp
      _ ≤ 192*(Q*r^2)*K :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide)) hKpos
      _ = _ := by ring
  exact ⟨hMainGuard, by omega, by rw [Nat.mul_assoc]; omega⟩

/-- At the exact ceiling logarithm used by MAIN, no comparison to
a real power of the input size is needed. -/
theorem ceiling_guards (N Q r : ℕ) (hN : 0 < N)
    (hL : 256 ≤ Nat.clog 2 (4*N))
    (hQ : Q ≤ Nat.clog 2 (4*N)) (hr : r^2 ≤ Nat.clog 2 (4*N)) (hrPos : 0 < r)
    (hPacking : (r^Q)^256 ≤ 2^(Nat.clog 2 (4*N))) :
    192*Q*r^2*r^Q+6 < N ∧
      10*(r^(2*Q))^2 ≤ 12*N ∧ 2*Q*r^2 ≤ 4*N := by
  let L := Nat.clog 2 (4*N)
  have hp : 2^(L-1) < 4*N := Nat.pow_pred_clog_lt_self (by decide) (by omega)
  have hLt : 1 ≤ L := by change 256 ≤ L at hL; omega
  have hEq : L-1+1 = L := Nat.sub_add_cancel hLt
  have hLower : 2^L ≤ 8*N := by
    calc
      _ = 2^(L-1)*2 := by rw [← pow_succ,hEq]
      _ ≤ (4*N)*2 := Nat.mul_le_mul_right _ hp.le
      _ = _ := by ring
  exact dyadic_guards N Q r L hL hLower hQ hr hrPos hPacking

#print axioms dyadic_guards
#print axioms ceiling_guards
end J1PhysicalParameters
