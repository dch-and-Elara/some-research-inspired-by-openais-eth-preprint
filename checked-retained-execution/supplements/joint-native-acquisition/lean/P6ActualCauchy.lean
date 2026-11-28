import P6ScopePrimitive
import J6R18ChildWriteKernel
import Mathlib.RingTheory.Nilpotent.Basic

open scoped Polynomial BigOperators Classical
open Polynomial NativeProbeRing P1DyadicGrid P1DyadicGridBridge
open AOracleSuccinctKernel AOracleSuccinctNative J6R9PacketLocal J6R18ChildWrite
namespace P6Joint
noncomputable section

theorem unit_actual_normFactor {R : Type*} [CommRing R] (p : ℕ)
    (hp : (2:R)^p=0) {a : ℕ} {t u : ℤ}
    (ht : t ∈ grid a) (hu : u ∈ (grid a).erase t) (z : R) :
    IsUnit (normFactor a t u z) := by
  have hne := (Finset.ne_of_mem_erase hu).symm
  have hv := grid_difference_valuation_le ht (Finset.mem_of_mem_erase hu) hne
  have hpos : 0 < a+1-padicValInt 2 (t-u) := by omega
  have hmul : IsNilpotent ((2:R)^(a+1-padicValInt 2 (t-u))*z) := by
    refine ⟨p,?_⟩
    rw [mul_pow, ← pow_mul, Nat.mul_comm _ p, pow_mul, hp, zero_pow hpos.ne', zero_mul]
  have hodd := (oddWord_factor (sub_ne_zero.mpr hne)).1
  have hunit : IsUnit ((oddWord (t-u):ℤ):R) :=
    J6ZeroTransport.oddCast_unit p hp _ fun h => (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  unfold normFactor shiftWord
  exact hmul.isUnit_add_left_of_commute hunit (Commute.all _ _)

theorem actual_cauchy_survives_unit (p : ℕ) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) {a : ℕ} {t k : ℤ} (ht : t ∈ grid a) (hk : k ∈ grid a)
    (hprec : a+1<p) (z : Scalar p f) (hz : IsUnit z) :
    (W a t k).eval₂ (J6ZeroTransport.reduceAt p (scalar_nilpotent p f)) z ≠ 0 := by
  let R := Scalar p f
  have hp := scalar_nilpotent p f
  rw [W_is_modular p hp ht hk]
  have hinv : IsUnit (oddInverse p (oddDerivative a:R)) :=
    isUnit_of_mul_eq_one _ _ (by simpa only [mul_comm] using inverse_int p hp _ (oddDerivative_odd a))
  have hprod (s : Finset ℤ) (hs : s ⊆ (grid a).erase t) :
      IsUnit (∏ q ∈ s, normFactor a t q z) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert q s hq ih =>
      rw [Finset.prod_insert hq]
      exact (unit_actual_normFactor p hp ht (hs (Finset.mem_insert_self _ _)) z).mul
        (ih (fun r hr => hs (Finset.mem_insert_of_mem hr)))
  by_cases hkT : k=t
  · simp only [modular, hkT, if_true]
    have hu := (hprod ((grid a).erase t) (fun _ h => h)).mul hinv
    simpa using dyadic_unit_survives p 0 (by omega) f hf hd _ hu
  · simp only [modular, hkT, if_false]
    let s := ((grid a).erase t).erase k
    have hu := (hz.mul (hprod s (Finset.erase_subset _ _))).mul hinv
    have h := dyadic_unit_survives p (a+1-padicValInt 2 (t-k)) (by omega) f hf hd _ hu
    simpa only [s, ← mul_assoc] using h

theorem nonzero_binary_probe_unit (p : ℕ) (hp : 0 < p)
    (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))]
    (addr : Fin f.natDegree → Bool) (h : addr ≠ (fun _ => false)) :
    IsUnit (probe p f addr) := by
  apply unit_of_residue p hp f hf
  intro hz
  have hzero : probe p f (fun _ => false) = 0 := by simp [probe,binaryPoly]
  apply h
  apply binary_residues_injective p hp f hf hd
  simpa only [Function.comp_apply, hzero, map_zero] using hz

#print axioms nonzero_binary_probe_unit

#print axioms unit_actual_normFactor
#print axioms actual_cauchy_survives_unit
end
end P6Joint
