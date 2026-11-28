import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

namespace J9PrintedSchedule

/-- Root parameters in the printed Appendix D, with ε=1/(128·1024). -/
def rootU (lambda : ℕ) : ℕ := lambda / (128 * 1024)
def rootA (lambda : ℕ) : ℕ := 2 * rootU lambda
def rootL (lambda : ℕ) : ℕ := 2 ^ rootA lambda

/-- Ceiling of s / floor(sqrt(lambda)) as printed in the leaf test. -/
def leafThreshold (s lambda : ℕ) : ℕ :=
  (s + lambda.sqrt - 1) / lambda.sqrt

/-- Finite packet packing array size at the printed palette r=64. -/
def arrayCard (a : ℕ) : ℕ := 64 ^ (2*a)

/-- Arithmetic parts of the D root recovery schedule. -/
def precision (p h D M a : ℕ) : ℕ := p + 8*h*D + 8*M*(a+1)
def degreeBound (M L : ℕ) : ℕ := M * (2*L-1)
def probeCount (M L : ℕ) : ℕ := degreeBound M L + 1

theorem rootU_range (lambda : ℕ) :
    131072 * rootU lambda ≤ lambda ∧ lambda < 131072 * (rootU lambda + 1) := by
  change 131072 * (lambda/131072) ≤ lambda ∧ lambda < 131072*(lambda/131072+1)
  omega

theorem rootU_two_iff (lambda : ℕ) : 2 ≤ rootU lambda ↔ 262144 ≤ lambda := by
  change 2 ≤ lambda / 131072 ↔ 262144 ≤ lambda
  omega

theorem rootL_ge_six_iff_u (lambda : ℕ) : 6 ≤ rootL lambda ↔ 2 ≤ rootU lambda := by
  constructor
  · intro h
    by_contra hn
    have he : rootU lambda = 0 ∨ rootU lambda = 1 := by omega
    rcases he with hu | hu <;> norm_num [rootL, rootA, hu] at h
  · intro h
    have ha : 4 ≤ rootA lambda := by unfold rootA; omega
    have hp : (2 : ℕ)^4 ≤ 2 ^ rootA lambda := Nat.pow_le_pow_right (by decide) ha
    exact (show 6 ≤ (2:ℕ)^4 by decide).trans hp

theorem rootL_ge_six_iff_lambda (lambda : ℕ) :
    6 ≤ rootL lambda ↔ 262144 ≤ lambda :=
  (rootL_ge_six_iff_u lambda).trans (rootU_two_iff lambda)

set_option exponentiation.threshold 262143 in
/-- For lambda=ceil(log_2 s), this is the exact finite J9 threshold,
rather than an asymptotic claim. Below it the root packet length is 1 or 4. -/
theorem rootL_ge_six_iff_size (s : ℕ) :
    6 ≤ rootL (Nat.clog 2 s) ↔ (2 : ℕ)^262143 < s := by
  exact (rootL_ge_six_iff_lambda _).trans
    (Nat.lt_clog_iff_pow_lt (b := 2) (by decide) (x := s) (y := 262143))

theorem arrayCard_power (a : ℕ) : arrayCard a = (2^a)^12 := by
  calc
    arrayCard a = ((2:ℕ)^6)^(2*a) := by norm_num [arrayCard]
    _ = (2 : ℕ)^(6*(2*a)) := (Nat.pow_mul 2 6 (2*a)).symm
    _ = (2^a)^12 := by rw [← Nat.pow_mul 2 a 12]; congr 1; omega

/-- The printed packing feasibility M >= L D_arr is stronger than L^3 <= M. -/
theorem cube_le_of_packing (a M : ℕ) (hPack : 2^a * arrayCard a ≤ M) :
    (2^a)^3 ≤ M := by
  rw [arrayCard_power] at hPack
  have hL : 0 < (2:ℕ)^a := Nat.pow_pos (by decide)
  have h13 : 2^a * ((2:ℕ)^a)^12 = ((2:ℕ)^a)^13 := by
    rw [← pow_succ']
  rw [h13] at hPack
  exact (Nat.pow_le_pow_right hL (by decide : (3 : ℕ) ≤ 13)).trans hPack

theorem next_le_two_power (a : ℕ) : a+1 ≤ (2:ℕ)^a := by
  induction a with
  | zero => decide
  | succ a ih =>
      rw [Nat.pow_succ]
      omega

/-- A finite strict cube bound from the raw root formulas, without
assuming feasibility of the stronger source packing test. -/
theorem cube_times_sqrt_le_pow (lambda : ℕ) (hU : 1 ≤ rootU lambda) :
    (rootL lambda)^3 * lambda.sqrt ≤ (2:ℕ)^(lambda-1) := by
  let u := rootU lambda
  have hu : 1 ≤ u := hU
  have h := rootU_range lambda
  change 131072 * u ≤ lambda ∧ lambda < 131072 * (u + 1) at h
  have hCube : (rootL lambda)^3 = (2:ℕ)^(6*u) := by
    unfold rootL rootA
    rw [← Nat.pow_mul]
    change (2 : ℕ)^((2*u)*3) = (2:ℕ)^(6*u)
    congr 1
    omega
  have hLog : lambda ≤ (2:ℕ)^(17+u) := by
    calc
      lambda ≤ 131072 * (u+1) := h.2.le
      _ ≤ 131072 * (2:ℕ)^u := Nat.mul_le_mul_left _ (next_le_two_power u)
      _ = (2:ℕ)^(17+u) := by rw [Nat.pow_add]
  have hExp : (6*u)+(17+u) ≤ lambda-1 := by omega
  calc
    (rootL lambda)^3 * lambda.sqrt ≤ (2:ℕ)^(6*u)*(2:ℕ)^(17+u) := by
      rw [hCube]
      exact Nat.mul_le_mul_left _ ((Nat.sqrt_le_self lambda).trans hLog)
    _ = (2:ℕ)^((6*u)+(17+u)) := (Nat.pow_add _ _ _).symm
    _ ≤ (2:ℕ)^(lambda-1) := Nat.pow_le_pow_right (by decide) hExp

theorem le_roundup_mul (s d : ℕ) (hd : 0 < d) :
    s ≤ ((s+d-1)/d)*d := by
  have hMod := Nat.mod_lt (s+d-1) hd
  have hSum : (s+d-1) % d + ((s+d-1)/d)*d = s+d-1 := by
    simpa only [Nat.mul_comm (((s+d-1)/d)) d] using Nat.mod_add_div (s+d-1) d
  omega

theorem root_cube_lt_active_M (s M : ℕ) (hU : 1 ≤ rootU (Nat.clog 2 s))
    (hActive : leafThreshold s (Nat.clog 2 s) < M) :
    (rootL (Nat.clog 2 s))^3 < M := by
  let lambda := Nat.clog 2 s
  have hu : 1 ≤ rootU lambda := hU
  have h := (rootU_range lambda).1
  have hPos : 0 < lambda := by omega
  have hd : 0 < lambda.sqrt := Nat.sqrt_pos.2 hPos
  have hpred : lambda-1 < Nat.clog 2 s := by change lambda-1 < lambda; omega
  have hs : (2:ℕ)^(lambda-1) < s :=
    (Nat.lt_clog_iff_pow_lt (b := 2) (by decide)).1 hpred
  have hLow := (cube_times_sqrt_le_pow lambda hu).trans_lt hs
  have hHigh : s ≤ M * lambda.sqrt := by
    calc
      s ≤ leafThreshold s lambda * lambda.sqrt := le_roundup_mul s lambda.sqrt hd
      _ ≤ M * lambda.sqrt := Nat.mul_le_mul_right _ hActive.le
  exact Nat.lt_of_mul_lt_mul_right (hLow.trans_le hHigh)

/-- t=L-1 is odd and thus uses the source's valuation-zero coordinate. -/
theorem root_outer_odd (lambda : ℕ) (hU : 1 ≤ rootU lambda) :
    (rootL lambda - 1) % 2 = 1 := by
  have hA : 0 < rootA lambda := by unfold rootA; omega
  have he : rootA lambda = (rootA lambda - 1) + 1 := by omega
  have hL : rootL lambda = (2^(rootA lambda-1):ℕ) * 2 := by
    calc
      rootL lambda = (2:ℕ)^((rootA lambda-1)+1) := congrArg (fun a : ℕ => (2:ℕ)^a) he
      _ = _ := by rw [Nat.pow_succ]
  have hp : 0 < (2:ℕ)^(rootA lambda-1) := Nat.pow_pos (by decide)
  rw [hL]
  omega

/-- Precision at the printed active node: its mandatory 8M(a+1) term
already suffices for 10M output bits. This is stronger than an eventual bound. -/
theorem precision_ge_sixteen_add_base (p h D M a : ℕ) (hA : 1 ≤ a) :
    p + 16*M ≤ precision p h D M a := by
  have h : M*16 ≤ M*(8*(a+1)) :=
    Nat.mul_le_mul_left M (by omega)
  have he : M*(8*(a+1)) = 8*M*(a+1) := by ring
  rw [he, Nat.mul_comm M 16] at h
  unfold precision
  omega

theorem precision_gt_ten (p h D M a : ℕ) (hP : 0 < p) (hA : 1 ≤ a) :
    10*M < precision p h D M a := by
  have h := precision_ge_sixteen_add_base p h D M a hA
  omega

/-- Source probe count M(2L−1)+1 contains the 10M+1-point J9 subgrid. -/
theorem probes_ge_ten_add_one (M L : ℕ) (hL : 6 ≤ L) :
    10*M + 1 ≤ probeCount M L := by
  have h := Nat.mul_le_mul_left M (show 10 ≤ 2*L - 1 by omega)
  unfold probeCount degreeBound
  rw [Nat.mul_comm 10 M]
  exact Nat.add_le_add_right h 1

/-- The J9 numerical checks from the raw printed size formulas and
the nonleaf test. No field-size or polynomial reconstruction is assumed. -/
theorem native_j9_numerics (s M p h D : ℕ) (hSize : (2:ℕ)^262143 < s)
    (hActive : leafThreshold s (Nat.clog 2 s) < M) (hP : 0 < p) :
    let lambda := Nat.clog 2 s
    (rootL lambda)^3 ≤ M ∧ 6 ≤ rootL lambda ∧
      10*M < precision p h D M (rootA lambda) ∧
      10*M + 1 ≤ probeCount M (rootL lambda) ∧ (rootL lambda - 1) % 2 = 1 := by
  let lambda := Nat.clog 2 s
  have hL : 6 ≤ rootL lambda := (rootL_ge_six_iff_size s).2 hSize
  have hU₂ := (rootL_ge_six_iff_u lambda).1 hL
  have hU₁ : 1 ≤ rootU lambda := by omega
  have hA : 1 ≤ rootA lambda := by unfold rootA; omega
  exact ⟨(root_cube_lt_active_M s M hU₁ hActive).le, hL, precision_gt_ten p h D M _
    hP hA, probes_ge_ten_add_one M _ hL, root_outer_odd lambda hU₁⟩


theorem root_cube_lt_size (s : ℕ) (hU : 1 ≤ rootU (Nat.clog 2 s)) :
    (rootL (Nat.clog 2 s))^3 < s := by
  let lambda := Nat.clog 2 s
  have h := (rootU_range lambda).1
  have hu : 1 ≤ rootU lambda := hU
  have hPos : 0 < lambda := by omega
  have hd : 0 < lambda.sqrt := Nat.sqrt_pos.2 hPos
  have hpred : lambda-1 < Nat.clog 2 s := by change lambda-1 < lambda; omega
  have hs : (2:ℕ)^(lambda-1) < s :=
    (Nat.lt_clog_iff_pow_lt (b := 2) (by decide)).1 hpred
  calc
    (rootL lambda)^3 = (rootL lambda)^3 * 1 := by rw [Nat.mul_one]
    _ ≤ (rootL lambda)^3 * lambda.sqrt := Nat.mul_le_mul_left _ hd
    _ ≤ (2:ℕ)^(lambda-1) := cube_times_sqrt_le_pow lambda hU
    _ < s := hs

/-- Purely numerical field supply bound: when the fixed linear wire
constant is at most s, the complete printed grid is smaller than 2^e.
The field construction and probe distinctness are separate theorems. -/
theorem all_probes_lt_residue_count (s M C : ℕ)
    (hU : 1 ≤ rootU (Nat.clog 2 s)) (hM : 1 ≤ M) (hWire : M ≤ C*s) (hC : C ≤ s) :
    probeCount M (rootL (Nat.clog 2 s)) < (2:ℕ)^(4*Nat.clog 2 s) := by
  let lambda := Nat.clog 2 s
  let L := rootL lambda
  have hCube : L^3 < s := root_cube_lt_size s hU
  have hu : 1 ≤ rootU lambda := hU
  have hL : 2 ≤ L := by
    have hA : 1 ≤ rootA lambda := by unfold rootA; omega
    exact Nat.pow_le_pow_right (show (0:ℕ) < 2 by decide) hA
  have hL2 : 2 ≤ L^2 := by
    calc
      2 ≤ L := hL
      _ = L*1 := (Nat.mul_one _).symm
      _ ≤ L*L := Nat.mul_le_mul_left _ (by omega)
      _ = L^2 := (pow_two _).symm
  have h2L : 2*L ≤ s := by
    calc
      2*L ≤ L^2*L := Nat.mul_le_mul_right _ hL2
      _ = L^3 := (Nat.pow_succ L 2).symm
      _ ≤ s := hCube.le
  have hMsq : M ≤ s^2 := hWire.trans (by simpa only [pow_two] using Nat.mul_le_mul_right s hC)
  have hPos : 0 < L^3 := Nat.pow_pos (by omega)
  have hs2 : 1 < s := by omega
  have hProbe : probeCount M L ≤ M*(2*L) := by
    calc
      probeCount M L = M*(2*L-1) + 1 := rfl
      _ ≤ M*(2*L-1) + M := Nat.add_le_add_left hM _
      _ = M*((2*L-1)+1) := by ring
      _ = M*(2*L) := by congr 1; omega
  have hq : s^4 ≤ (2:ℕ)^(4*lambda) := by
    rw [Nat.mul_comm 4 lambda, Nat.pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : (1:ℕ) < 2) s) 4
  calc
    probeCount M L ≤ M*(2*L) := hProbe
    _ ≤ s^2*s := Nat.mul_le_mul hMsq h2L
    _ = s^3 := (Nat.pow_succ s 2).symm
    _ < s^4 := Nat.pow_lt_pow_right hs2 (by decide)
    _ ≤ (2:ℕ)^(4*lambda) := hq


/-- The weak cube inequality is unconditional on u on the raw nonleaf
size test (the degenerate u=0 has L=1). -/
theorem root_cube_le_active_M (s M : ℕ)
    (hActive : leafThreshold s (Nat.clog 2 s) < M) :
    (rootL (Nat.clog 2 s))^3 ≤ M := by
  by_cases h : 1 ≤ rootU (Nat.clog 2 s)
  · exact (root_cube_lt_active_M s M h hActive).le
  · have he : rootU (Nat.clog 2 s) = 0 := by omega
    have hp : 1 ≤ M := by omega
    simpa [rootL, rootA, he] using hp

/-- The numerical 10M+1 subgrid condition is itself sharp for M>0. -/
theorem probes_ge_ten_add_one_iff {M L : ℕ} (hM : 0 < M) :
    10*M + 1 ≤ probeCount M L ↔ 6 ≤ L := by
  constructor
  · intro h
    by_contra hn
    have h' := Nat.mul_le_mul_left M (show 2*L-1 ≤ 9 by omega)
    have h9 : probeCount M L ≤ 9*M + 1 := by
      unfold probeCount degreeBound
      have hh := Nat.add_le_add_right h' 1
      simpa [Nat.mul_comm M 9] using hh
    omega
  · exact probes_ge_ten_add_one M L

/-- The selected odd node's valuation-zero Hermite order is nonzero:
ceil(3M/u) times u is positive for M,u>0. -/
theorem odd_node_multiplicity_pos (M u : ℕ) (hM : 0 < M) (hu : 0 < u) :
    0 < ((3*M + u - 1) / u) * u := by
  exact (show 0 < 3*M by omega).trans_le (le_roundup_mul (3*M) u hu)

#print axioms root_cube_le_active_M
#print axioms probes_ge_ten_add_one_iff
#print axioms odd_node_multiplicity_pos
#print axioms all_probes_lt_residue_count
#print axioms rootL_ge_six_iff_size
#print axioms arrayCard_power
#print axioms cube_le_of_packing
#print axioms cube_times_sqrt_le_pow
#print axioms root_cube_lt_active_M
#print axioms root_outer_odd
#print axioms precision_gt_ten
#print axioms probes_ge_ten_add_one
#print axioms native_j9_numerics

end J9PrintedSchedule
