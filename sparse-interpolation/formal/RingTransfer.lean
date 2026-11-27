import SymbolicMinors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Group.Torsion

open Matrix Polynomial

namespace Round4Transfer

open GrenetMcCoy

variable {R S ι K : Type*}

def progression [CommRing R] (offset : ι → ℕ) (a b : R) : ι → R :=
  fun i => a + (offset i : R) * b

/-- Carry a symbolic unit-ideal certificate back along any embedding into
a commutative rational algebra in which the step is invertible. -/
theorem progression_injective_of_embedding [CommRing R] [CommRing S]
    (offset : ι → ℕ) (E : Finset ℕ) (a b : R)
    (f : R →+* S) (hf : Function.Injective f)
    (q : ℚ →+* S) (hb : IsUnit (f b))
    (hE : fullMinorIdeal (symbolicMatrix offset E) = ⊤) :
    Function.Injective (evaluationMatrix (progression offset a b) E).mulVec := by
  obtain ⟨u, hu⟩ := hb
  let z : S := f a * ↑u⁻¹
  have hpoints (i : ι) :
      f (progression offset a b i) = (z + (offset i : S)) * (u : S) := by
    simp [progression, z, ← hu, add_mul, mul_assoc]
  have hnorm := normalized_injective offset E q z hE
  have hker (c : E → R) (hc : (evaluationMatrix (progression offset a b) E) *ᵥ c = 0) :
      c = 0 := by
    let y : E → S := fun e => (u : S) ^ e.val * f (c e)
    have hy : (evaluationMatrix (fun i => z + (offset i : S)) E) *ᵥ y = 0 := by
      funext i
      calc
        _ = ∑ e : E, f ((progression offset a b i) ^ e.val * c e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          change (z + (offset i : S)) ^ e.val * ((u : S) ^ e.val * f (c e)) = _
          rw [map_mul, map_pow, hpoints, mul_pow, mul_assoc]
        _ = f (((evaluationMatrix (progression offset a b) E) *ᵥ c) i) := by
          exact (map_sum f _ _).symm
        _ = 0 := by rw [hc]; exact map_zero f
    have hy0 : y = 0 := hnorm (hy.trans (Matrix.mulVec_zero _).symm)
    funext e
    apply hf
    change f (c e) = f 0
    rw [map_zero]
    exact (u.isUnit.pow e.val).mul_right_eq_zero.mp (congrFun hy0 e)
  intro v w he
  apply sub_eq_zero.mp
  apply hker
  rw [Matrix.mulVec_sub, he, sub_self]

private abbrev Total (R : Type*) [CommRing R] :=
  Localization (nonZeroDivisors R)

private theorem intCast_regular [CommRing R] [IsAddTorsionFree R] {n : ℤ}
    (hn : n ≠ 0) : (n : R) ∈ nonZeroDivisors R := by
  apply mem_nonZeroDivisors_iff_right.mpr
  intro x hx
  apply zsmul_right_injective hn
  change n • x = n • (0 : R)
  rw [zsmul_eq_mul, zsmul_zero, mul_comm]
  exact hx

/-- Integer torsion freeness supplies the map from Q to the localization
at the regular elements of the original ring. -/
private noncomputable def rationalsToTotal (R : Type*) [CommRing R] [IsAddTorsionFree R] :
    ℚ →+* Total R :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ)
    (g := (algebraMap R (Total R)).comp (Int.castRingHom R)) fun n =>
      IsLocalization.map_units (Total R)
        ⟨(n.val : R), intCast_regular (mem_nonZeroDivisors_iff_ne_zero.mp n.property)⟩

/-- Per-support transfer to any additive-torsion-free commutative ring
with a regular step, including rings with zero divisors. -/
theorem progression_injective_of_symbolic_unit_ideal [CommRing R] [IsAddTorsionFree R]
    (offset : ι → ℕ) (E : Finset ℕ) (a b : R) (hb : b ∈ nonZeroDivisors R)
    (hE : fullMinorIdeal (symbolicMatrix offset E) = ⊤) :
    Function.Injective (evaluationMatrix (progression offset a b) E).mulVec :=
  progression_injective_of_embedding offset E a b (algebraMap R (Total R))
    (IsLocalization.injective (Total R) le_rfl)
    (rationalsToTotal R) (IsLocalization.map_units (Total R) ⟨b, hb⟩) hE

/-- Exact same-ring recovery, with no bound on the exponents. -/
def DeterminesUnboundedSparse [CommRing R] (x : ι → R) (t : ℕ) : Prop :=
  ∀ f g : R[X], f.support.card ≤ t → g.support.card ≤ t →
    (∀ i, f.eval (x i) = g.eval (x i)) → f = g

/-- The support certificate needs to range over exactly 2t columns.
The degree bound used internally comes from the two candidate inputs. -/
theorem determinesUnboundedSparse_of_symbolic_unit_ideals [CommRing R] [IsAddTorsionFree R]
    (offset : ι → ℕ) (a b : R) (hb : b ∈ nonZeroDivisors R) (t : ℕ)
    (hE : ∀ E : Finset ℕ, E.card = 2 * t → fullMinorIdeal (symbolicMatrix offset E) = ⊤) :
    DeterminesUnboundedSparse (progression offset a b) t := by
  intro f g hf hg hs
  let d := max f.natDegree g.natDegree + 2 * t
  have hsize : min (2 * t) (d + 1) = 2 * t := min_eq_left (by dsimp [d]; omega)
  have hd : DeterminesSparse (progression offset a b) d t := by
    apply (determinesSparse_iff_max_support_matrices _ _ _).mpr
    intro E _ hcard
    exact progression_injective_of_symbolic_unit_ideal offset E a b hb (hE E (hcard.trans hsize))
  exact hd f g ⟨by dsimp [d]; omega, hf⟩ ⟨by dsimp [d]; omega, hg⟩ hs

def eightOffsets (i : Fin 8) : ℕ := i.val

theorem eight_samples_of_symbolic_unit_ideals [CommRing R] [IsAddTorsionFree R]
    (a b : R) (hb : b ∈ nonZeroDivisors R)
    (hE : ∀ E : Finset ℕ, E.card = 4 → fullMinorIdeal (symbolicMatrix eightOffsets E) = ⊤) :
    DeterminesUnboundedSparse (progression eightOffsets a b) 2 :=
  determinesUnboundedSparse_of_symbolic_unit_ideals eightOffsets a b hb 2 hE

/-- An algebraically closed field calculation can supply the four-column
certificates. The conclusion is entirely in the original ring. -/
theorem eight_samples_of_no_common_root [CommRing R] [IsAddTorsionFree R]
    [Field K] [IsAlgClosed K] (a b : R) (hb : b ∈ nonZeroDivisors R) (q : ℚ →+* K)
    (hE : ∀ (E : Finset ℕ), E.card = 4 → ∀ z : K, ∃ rows : E → Fin 8,
      ((evaluationMatrix (fun i => z + (eightOffsets i : K)) E).submatrix rows id).det ≠ 0) :
    DeterminesUnboundedSparse (progression eightOffsets a b) 2 :=
  eight_samples_of_symbolic_unit_ideals a b hb fun E hcard =>
    symbolic_fullMinorIdeal_eq_top_of_no_common_root eightOffsets E q (hE E hcard)

theorem eight_samples_of_pointwise_injective [CommRing R] [IsAddTorsionFree R]
    [Field K] [IsAlgClosed K] (a b : R) (hb : b ∈ nonZeroDivisors R) (q : ℚ →+* K)
    (hE : ∀ (E : Finset ℕ), E.card = 4 → ∀ z : K,
      Function.Injective (evaluationMatrix (fun i => z + (eightOffsets i : K)) E).mulVec) :
    DeterminesUnboundedSparse (progression eightOffsets a b) 2 :=
  eight_samples_of_symbolic_unit_ideals a b hb fun E hcard =>
    symbolic_fullMinorIdeal_eq_top_of_pointwise_injective eightOffsets E q (hE E hcard)

end Round4Transfer
