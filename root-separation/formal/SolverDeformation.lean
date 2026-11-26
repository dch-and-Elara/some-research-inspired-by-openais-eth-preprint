import SolverReadout
import SolverNetwork
import RootProgram
import S11Taper

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial
open scoped BigOperators

section Generic

variable {K : Type*} [Field K] [CharZero K] (N : Network K)
variable {P : Type} [DecidableEq P] {a : ℕ} (place : N.Wire ↪ P × Fin (2^a))

open Classical in
def normalizedDeformation : K[X] :=
  (deformed N.rowProduct N.colProduct place).comp (C ((2 : K)^(a+1)) * X)

theorem normalizedDeformation_origin :
    (normalizedDeformation N place).eval 0 = N.contract := by
  classical
  simp only [normalizedDeformation, eval_comp, eval_mul, eval_C, eval_X, mul_zero]
  exact deformed_origin N.rowProduct N.colProduct place

open Classical in
theorem normalizedDeformation_center (t : ℤ) (z : K) :
    (normalizedDeformation N place).eval (S7.scaledCenter a t + z) =
      (deformed N.rowProduct N.colProduct place).eval ((t:K) + (2:K)^(a+1)*z) := by
  classical
  simp only [normalizedDeformation, eval_comp, eval_mul, eval_C, eval_X]
  congr 1
  unfold S7.scaledCenter
  have h : (2:K)^(a+1) ≠ 0 := pow_ne_zero _ (NeZero.ne 2)
  field_simp

theorem normalizedDeformation_local (t : ℤ) :
    ((normalizedDeformation N place).comp (X+C (S7.scaledCenter a t))).degree <
      ↑(probeCount (Fintype.card N.Wire) (2^a)) := by
  classical
  have hh : (C ((2:K)^(a+1)) * X : K[X]).comp (X+C (S7.scaledCenter a t)) =
      C (t:K) + C ((2:K)^(a+1)) * X := by
    rw [mul_comp, C_comp, X_comp, mul_add, ← C_mul]
    have hn : (2:K)^(a+1) ≠ 0 := pow_ne_zero _ (NeZero.ne 2)
    rw [show (2:K)^(a+1) * S7.scaledCenter a t = (t:K) by
      unfold S7.scaledCenter
      field_simp]
    exact add_comm _ _
  rw [normalizedDeformation, comp_assoc, hh]
  exact local_degree_bound _ _ (deformed_degree _ _ place) _ _

theorem normalizedDeformation_window (u : ℕ) (hM : 0 < Fintype.card N.Wire)
    (hu : 0 < u) (ha : 0 < a) :
    (normalizedDeformation N place).degree <
      ↑(∑ t : Active a u, multiplicity (Fintype.card N.Wire) u t.val) := by
  classical
  have he : Even (2^a) := even_two.pow_of_ne_zero ha.ne'
  have ht := taper_degree_window hu hM (by positivity : 0 < 2^a) he
  rw [← Finset.sum_attach (centers u (2^a)) (multiplicity (Fintype.card N.Wire) u)] at ht
  have hd : (normalizedDeformation N place).natDegree ≤ Fintype.card N.Wire * (2*2^a-1) := by
    unfold normalizedDeformation
    have hc : (C ((2:K)^(a+1)) * X : K[X]).natDegree ≤ 1 := by
      simpa only [pow_one] using natDegree_C_mul_X_pow_le ((2:K)^(a+1)) 1
    refine (natDegree_comp_le (p := deformed N.rowProduct N.colProduct place)
      (q := C ((2:K)^(a+1)) * X)).trans ?_
    exact (Nat.mul_le_mul (deformed_degree _ _ place) hc).trans (by simp)
  exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.2 (hd.trans_lt ht))

end Generic

section FourthPaper
open Entry GraphCutMoments
variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (σ : V → Bool)
variable (hn : bigRoot (n (V := V))) {K : Type*} [Field K] [CharZero K]

def rootDeformation : K[X] :=
  normalizedDeformation (entryNetwork E reg σ K) (chosenPacking E reg hn).position

theorem rootDeformation_origin :
    (rootDeformation E reg σ hn : K[X]).eval 0 =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : K) := by
  rw [rootDeformation, normalizedDeformation_origin, entryNetwork_contract]

theorem rootDeformation_local (t : ℤ) :
    ((rootDeformation E reg σ hn : K[X]).comp (X+C (S7.scaledCenter (rootA E) t))).degree <
      ↑(probeCount (rootM E) (rootL E)) :=
  normalizedDeformation_local (entryNetwork E reg σ K) (chosenPacking E reg hn).position t

theorem rootDeformation_window :
    (rootDeformation E reg σ hn : K[X]).degree <
      ↑(∑ t : Active (rootA E) (rootU E), multiplicity (rootM E) (rootU E) t.val) := by
  have hu := (root_certified E reg hn).1
  have hm := wire_count E reg
  have hlarge := bigRoot_n hn
  have ha : rootA E = 2*rootU E := (root_parameters (size E)).1
  have hmpos : 0 < rootM E := by
    change 0 < Fintype.card (Wire E)
    rw [hm]
    exact Nat.mul_pos (by decide) (by omega)
  have hapos : 0 < rootA E := by rw [ha]; exact Nat.mul_pos (by decide) hu
  exact normalizedDeformation_window (entryNetwork E reg σ K)
    (chosenPacking E reg hn).position _ hmpos hu hapos

end FourthPaper

#print axioms normalizedDeformation_center
#print axioms normalizedDeformation_local
#print axioms normalizedDeformation_window
#print axioms rootDeformation_origin
#print axioms rootDeformation_window

end RootSeparation.Solver
