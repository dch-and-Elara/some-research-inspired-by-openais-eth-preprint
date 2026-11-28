import J6Mesh
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-! Exact native two-level J6 recovery: centered integer lifting, removal
of public factors, signed odd power inversion, and the final rational
interpolation. The physical realization and integer fitting are explicit
hypotheses at the residue interface. -/
namespace J6Recovery
open LayerRecovery
open scoped BigOperators Polynomial
noncomputable section
variable {P T : Type*} [Fintype P] [DecidableEq P] [Fintype T] [DecidableEq T]

abbrev Addr (m : ℕ) := Fin (m+1)
def exp (m : ℕ) (i : Addr m) := J6Mesh.L m-J6Mesh.index m i

theorem odd_exp (m : ℕ) (i : Addr m) : Odd (exp m i) := by
  obtain ⟨k,hk⟩ := (J6Mesh.mesh_seats m).2.2
  obtain ⟨j,hj⟩ := (J6Mesh.address_index m i).2.1
  have ht := (J6Mesh.address_index m i).2.2.2
  have hj' : J6Mesh.index m i = 2*j+1 := hj
  unfold exp
  use k-j-1
  omega

/-- Complete finite sum of the matched layers and independent boundary
and padding bits, with all exponent multiplicities tied to the legal address. -/
def layerSum (m q : ℕ) (A B : (P → Bool) → ℚ) (n : Addr m → T → ℕ)
    (i : Addr m) : ℚ :=
  let c := J6Mesh.point m i
  ∑ y : Fin (exp m i) → (P → Bool) × (P → Bool),
    ∑ _x : Fin (J6Mesh.index m i) → (Fin q → Bool), ∑ p : T → Bool,
    (∏ h, A (y h).1 * B (y h).2 * ∏ j : P,
      if (y h).1 j then (if (y h).2 j then c else 0)
        else 1 - if (y h).2 j then c else 0) *
      ∏ j : T, (if p j then 1-c else 1) ^ n i j

def publicFactor (m q : ℕ) (n : Addr m → T → ℕ) (i : Addr m) : ℚ :=
  (2:ℚ) ^ (q*J6Mesh.index m i) * ∏ j : T, (1 + (1-J6Mesh.point m i)^n i j)

omit [DecidableEq T] in
theorem publicFactor_pos (m q : ℕ) (n : Addr m → T → ℕ) (i : Addr m) :
    0 < publicFactor m q n i := by
  unfold publicFactor
  apply mul_pos (by positivity)
  have hc := (J6Mesh.negative_distinct_points m).1 i
  have h : 0 < 1-J6Mesh.point m i := by linarith
  exact Finset.prod_pos (fun j _ => add_pos_of_pos_of_nonneg (by norm_num) (pow_nonneg h.le _))

theorem layerSum_factorization (m q : ℕ) (A B : (P → Bool) → ℚ)
    (n : Addr m → T → ℕ) (i : Addr m) :
    layerSum m q A B n i =
    publicFactor m q n i * ((layerPolynomial A B).eval (J6Mesh.point m i))^exp m i := by
  unfold layerSum publicFactor
  rw [planted_layer_factorization]
  simp [mul_right_comm]

def oddRoot (k : ℕ) (x : ℚ) : ℚ := by
  classical
  exact if h : ∃ y : ℚ, y^k = x then Classical.choose h else 0

theorem oddRoot_correct {k : ℕ} (he : Odd k) (y : ℚ) : oddRoot k (y^k) = y := by
  have h : ∃ z : ℚ, z^k = y^k := ⟨y,rfl⟩
  unfold oddRoot
  rw [dif_pos h]
  exact (he.strictMono_pow (R := ℚ)).injective (Classical.choose_spec h)

def observation (m q : ℕ) (n : Addr m → T → ℕ) (prec : Addr m → ℕ)
    (d : Addr m → ℤ) (val : ∀ i, ZMod (2^prec i)) (i : Addr m) : ℚ :=
  (((d i : ZMod (2^prec i))^J6Mesh.M m * val i).valMinAbs : ℚ) /
    ((d i : ℚ)^J6Mesh.M m * publicFactor m q n i)

def reconstructed (m q : ℕ) (n : Addr m → T → ℕ) (prec : Addr m → ℕ)
    (d : Addr m → ℤ) (val : ∀ i, ZMod (2^prec i)) : ℚ[X] :=
  Lagrange.interpolate Finset.univ (J6Mesh.point m)
    (fun i => oddRoot (exp m i) (observation m q n prec d val i))

/-- The same native residues suffice for every input layer polynomial on
a fixed packing, with no sign or nonzero assumptions on the unknown values. -/
theorem recover_from_centered_physical_residues (m q : ℕ)
    (A B : (P → Bool) → ℚ) (hPorts : Fintype.card P ≤ m)
    (n : Addr m → T → ℕ) (prec : Addr m → ℕ) (d a : Addr m → ℤ)
    (val : ∀ i, ZMod (2^prec i))
    (hd : ∀ i, d i ≠ 0)
    (fits : ∀ i, 2*|a i| < (↑((2:ℕ)^prec i):ℤ))
    (residue : ∀ i, (d i : ZMod (2^prec i))^J6Mesh.M m * val i = (a i : ZMod (2^prec i)))
    (physical : ∀ i, (a i : ℚ) = (d i : ℚ)^J6Mesh.M m * layerSum m q A B n i) :
    reconstructed m q n prec d val = layerPolynomial A B := by
  have he (i : Addr m) : oddRoot (exp m i) (observation m q n prec d val i) =
      (layerPolynomial A B).eval (J6Mesh.point m i) := by
    letI : NeZero ((2:ℕ)^prec i) := ⟨pow_ne_zero _ (by decide)⟩
    have lift :
        ((d i : ZMod (2^prec i))^J6Mesh.M m * val i).valMinAbs = a i := by
      apply (ZMod.valMinAbs_spec _ _).mpr
      refine ⟨residue i,?_⟩
      have hf := fits i
      change -(↑((2:ℕ)^prec i):ℤ) < a i*2 ∧ a i*2 ≤ ↑((2:ℕ)^prec i)
      constructor <;> linarith [le_abs_self (a i),neg_le_abs (a i)]
    unfold observation
    rw [lift,physical i,layerSum_factorization,← mul_assoc]
    rw [mul_div_cancel_left₀]
    · exact oddRoot_correct (odd_exp m i) _
    · exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hd i)) (publicFactor_pos m q n i).ne'
  have hn : (layerPolynomial A B).natDegree < (Finset.univ : Finset (Addr m)).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    exact lt_of_le_of_lt (layerPolynomial_degree A B) (by omega)
  have hdegree : (layerPolynomial A B).degree < ↑(Finset.univ : Finset (Addr m)).card :=
    Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hn)
  symm
  exact Lagrange.eq_interpolate_of_eval_eq (fun i => oddRoot (exp m i) (observation m q n prec d val i))
    (J6Mesh.negative_distinct_points m).2.injOn hdegree
    (fun i _ => (he i).symm)

/-- The last readout performs Boolean identity wiring and yields the exact
old-row/new-column count, not only an unidentified interpolating polynomial. -/
theorem recovered_identity_count (m q : ℕ)
    (A B : (P → Bool) → ℚ) (hPorts : Fintype.card P ≤ m)
    (n : Addr m → T → ℕ) (prec : Addr m → ℕ) (d a : Addr m → ℤ)
    (val : ∀ i, ZMod (2^prec i))
    (hd : ∀ i, d i ≠ 0)
    (fits : ∀ i, 2*|a i| < (↑((2:ℕ)^prec i):ℤ))
    (residue : ∀ i, (d i : ZMod (2^prec i))^J6Mesh.M m * val i = (a i : ZMod (2^prec i)))
    (physical : ∀ i, (a i : ℚ) = (d i : ℚ)^J6Mesh.M m * layerSum m q A B n i) :
    (reconstructed m q n prec d val).eval 1 = ∑ x : P → Bool, A x * B x := by
  rw [recover_from_centered_physical_residues m q A B hPorts n prec d a val hd fits residue physical,
    layerPolynomial_eval_one]

#print axioms odd_exp
#print axioms layerSum_factorization
#print axioms recover_from_centered_physical_residues
#print axioms recovered_identity_count
end
end J6Recovery
