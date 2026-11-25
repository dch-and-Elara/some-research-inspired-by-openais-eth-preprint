import FiniteGrowth
import Mathlib.Data.Nat.Log

/-!
# An explicit threshold for logarithmic coordinate counts

All bounds are finite. An elementary bound on a cube by a power of two
supplies a threshold for any fixed multiple of a squared binary logarithm.
The application gives both the number of separated terms and a squared
lower bound for the integer exponent.
-/

namespace LogarithmicBudget

open scoped BigOperators

theorem cube_le_pow (k : ℕ) (hk : 10 ≤ k) : k ^ 3 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hstep : (k + 1) ^ 3 ≤ 2 * k ^ 3 := by
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hk
      ring_nf
      omega
    exact hstep.trans ((Nat.mul_le_mul_left 2 ih).trans_eq (pow_succ' 2 k).symm)

/-- A finite sufficient threshold for a squared coordinate count. -/
theorem quadratic_lt_of_exp (C u N : ℕ) (hu : 10 ≤ u) (hC : C < u) (hN : 2 ^ u ≤ N) :
    C * u ^ 2 < N := by
  calc
    _ < u * u ^ 2 := Nat.mul_lt_mul_of_pos_right hC (Nat.pow_pos (by omega))
    _ = u ^ 3 := by ring
    _ ≤ 2 ^ u := cube_le_pow u hu
    _ ≤ _ := hN

/-- A single explicit cutoff for all N at and beyond it. -/
def cutoff (C a : ℕ) : ℕ := 2 ^ max 10 (max a (4 * C + 1))

theorem log_square_lt (C a N : ℕ) (h : cutoff C a ≤ N) : C * (N.log2 + a) ^ 2 < N := by
  have hn : 0 < N := (Nat.two_pow_pos _).trans_le h
  have hk : max 10 (max a (4 * C + 1)) ≤ N.log2 := (Nat.le_log2 hn.ne').2 h
  have hten : 10 ≤ N.log2 := (le_max_left _ _).trans hk
  have ha : a ≤ N.log2 := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hc : 4 * C < N.log2 := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  calc
    _ ≤ C * (2 * N.log2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = (4 * C) * N.log2 ^ 2 := by ring
    _ < N := quadratic_lt_of_exp _ _ _ hten hc (Nat.log2_self_le hn.ne')

/-- Number of published active coordinates as an integer upper logarithm and
integer quotient. -/
def activeCoordinates (s : ℕ) : ℕ := Nat.clog 2 s / 131072

private theorem clog_le_log_add_three (N s : ℕ) (hs : s ≤ 4 * N) :
    Nat.clog 2 s ≤ N.log2 + 3 := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
  calc
    s ≤ 4 * N := hs
    _ ≤ 4 * 2 ^ (N.log2 + 1) := Nat.mul_le_mul_left _ (Nat.lt_log2_self (n := N)).le
    _ = 2 ^ (N.log2 + 3) := by rw [show N.log2 + 3 = (N.log2 + 1) + 2 by omega, pow_add]; ring

/-- In particular this applies to s = 7N/2. -/
theorem activeCoordinates_le_log (N s : ℕ) (hs : s ≤ 4 * N) :
    activeCoordinates s ≤ N.log2 + 3 :=
  (Nat.div_le_self _ _).trans (clog_le_log_add_three N s hs)

theorem source_coordinates_le_log (N : ℕ) : activeCoordinates (7 * N / 2) ≤ N.log2 + 3 :=
  activeCoordinates_le_log N _ (by omega)

/-- The complete source root uses a = 2u coordinates. -/
theorem source_root_coordinates_le_log (N : ℕ) :
    2 * activeCoordinates (7 * N / 2) ≤ N.log2 + 3 := by
  let n := Nat.clog 2 (7 * N / 2)
  calc
    _ ≤ 131072 * (n / 131072) := Nat.mul_le_mul_right _ (by decide : 2 ≤ 131072)
    _ ≤ n := Nat.mul_div_le _ _
    _ ≤ _ := clog_le_log_add_three N _ (by omega)

/-- Round up the fixed coefficient in front of u² in the size threshold. -/
def multiplier (k₀ h₀ t : ℚ) : ℕ := ⌈7776 * k₀ * h₀ / t ^ 2⌉₊

theorem logarithmic_threshold (N u a : ℕ) (k H t k₀ h₀ : ℚ) (ht : 0 < t) (hk : 0 ≤ k)
    (hmenu : k ≤ k₀ * u) (hscale : H ^ 2 ≤ h₀ * u)
    (hu : u ≤ N.log2 + a) (hN : cutoff (multiplier k₀ h₀ t) a ≤ N) :
    7776 * k * H ^ 2 / t ^ 2 < N := by
  let C := multiplier k₀ h₀ t
  have hround : 7776 * k₀ * h₀ / t ^ 2 ≤ (C : ℚ) := Nat.le_ceil _
  have hnat : C * u ^ 2 < N :=
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hu 2)).trans_lt (log_square_lt C a N hN)
  have hq : (C : ℚ) * (u : ℚ) ^ 2 < (N : ℚ) := by exact_mod_cast hnat
  apply FiniteGrowth.threshold_of_linear_caps (N : ℚ) k H t u k₀ h₀ ht hk hmenu hscale
  apply (div_lt_iff₀ (sq_pos_of_pos ht)).mp
  calc
    _ = (7776 * k₀ * h₀ / t ^ 2) * (u : ℚ) ^ 2 := by ring
    _ ≤ (C : ℚ) * (u : ℚ) ^ 2 := mul_le_mul_of_nonneg_right hround (sq_nonneg _)
    _ < _ := hq

/-- A rational squared form of d ≥ tN/(2√(h₀u)). -/
theorem squared_exponent (N t H h₀ u d : ℚ) (hN : 0 ≤ N) (ht : 0 ≤ t) (hH : 0 < H)
    (hd : 0 ≤ d) (hscale : H ^ 2 ≤ h₀ * u) (hlower : t * N / (2 * H) ≤ d) :
    (t * N) ^ 2 ≤ 4 * h₀ * u * d ^ 2 := by
  have hlin := (div_le_iff₀ (mul_pos (by norm_num) hH)).mp hlower
  calc
    _ ≤ (d * (2 * H)) ^ 2 := (sq_le_sq₀ (mul_nonneg ht hN)
      (mul_nonneg hd (mul_nonneg (by norm_num) hH.le))).2 hlin
    _ = 4 * H ^ 2 * d ^ 2 := by ring
    _ ≤ 4 * (h₀ * u) * d ^ 2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by norm_num)) (sq_nonneg d)
    _ = _ := by ring

variable {V I A J T R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype J] [Nonempty J] [Fintype T] [CommRing R] [CommRing S] [Nontrivial S] [Field K]
variable {E : Finset (V × V)} {L : V → I → A} {owner : J → I} {symbols : J → Finset A}

/-- From logarithmic coordinate count, linear menu and squared-scale caps,
and a single fixed cutoff, obtain a natural exponent on the actual modular
output. Its squared lower bound avoids introducing real square roots. -/
theorem logarithmic_modular_barrier (G : ExpanderBarrier.LabelGeometry E L owner symbols)
    (u a : ℕ) (k₀ h₀ : ℚ) (hh₀ : 0 ≤ h₀) (hmenu : (Fintype.card J : ℚ) ≤ k₀ * u)
    (hscale : G.H ^ 2 ≤ h₀ * u) (hu : u ≤ (Fintype.card V).log2 + a)
    (hN : cutoff (multiplier k₀ h₀ (FiniteGrowth.coefficient G.gamma G.eta)) a ≤ Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R) (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ z, (terms z).side = EmpiricalCutMoments.labelCut L owner symbols (assigned z))
    (hrepresentation : ∀ σ, embed (output σ) = ∑ z, (terms z).value σ)
    (hcorrect : ∀ σ, residue (output σ) = (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma G.eta * Fintype.card V) ^ 2 ≤
      4 * h₀ * (((Fintype.card V).log2 + a : ℕ) : ℚ) * (d : ℚ) ^ 2 ∧
      2 ^ d ≤ Fintype.card T := by
  have ht := FiniteGrowth.coefficient_pos G.gamma_pos G.eta_pos
  have hsz := logarithmic_threshold (Fintype.card V) u a (Fintype.card J) G.H _
    k₀ h₀ ht (Nat.cast_nonneg _) hmenu hscale hu hN
  obtain ⟨hl, hh⟩ := FiniteGrowth.modular_growth_barrier G hsz embed residue hinjective
    output terms assigned hside hrepresentation hcorrect
  refine ⟨⌊ExpanderBarrier.margin G⌋₊, ?_, hh⟩
  apply squared_exponent _ _ G.H _ _ _ (Nat.cast_nonneg _) ht.le
    (zero_lt_one.trans_le G.H_ge_one) (Nat.cast_nonneg _) _ hl
  exact hscale.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hu) hh₀)

#print axioms cube_le_pow
#print axioms quadratic_lt_of_exp
#print axioms log_square_lt
#print axioms activeCoordinates_le_log
#print axioms source_coordinates_le_log
#print axioms source_root_coordinates_le_log
#print axioms logarithmic_threshold
#print axioms squared_exponent
#print axioms logarithmic_modular_barrier

end LogarithmicBudget
