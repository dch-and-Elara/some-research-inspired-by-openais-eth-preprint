import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-! Cyclic length statements used for Paper 5, v7 (A.10). We use actual
Mathlib module length, not a proxy that identifies a finite ring with its
residue field. A nonzero generator of a principal maximal ideal suffices. -/
namespace Paper5
open scoped BigOperators

variable {R : Type*} [CommRing R] [IsDomain R]

abbrev PowIdeal (π : R) (s : ℕ) : Ideal R :=
  Ideal.span ({π^s} : Set R)

abbrev Cyclic (π : R) (s : ℕ) := R ⧸ PowIdeal π s

def powAction (π : R) (s : ℕ) (M : Type*) [AddCommGroup M] [Module R M] :
    M →ₗ[R] M :=
  π^s • LinearMap.id

omit [IsDomain R] in
@[simp] theorem powAction_apply (π : R) (s : ℕ) (M : Type*)
    [AddCommGroup M] [Module R M] (x : M) :
    powAction π s M x = π^s • x := rfl

abbrev PowerImage (π : R) (s : ℕ) (M : Type*) [AddCommGroup M] [Module R M] :=
  LinearMap.range (powAction π s M)

theorem pow_dvd_pow_mul_iff (π : R) (hπ : π ≠ 0) (q t : ℕ) (x : R) :
    π^q ∣ π^t*x ↔ π^(q-t) ∣ x := by
  by_cases ht : t≤q
  · have he : π^q = π^t*π^(q-t) := by rw [←pow_add,Nat.add_sub_of_le ht]
    rw [he]
    exact mul_dvd_mul_iff_left (pow_ne_zero _ hπ)
  · have hq : q≤t := by omega
    have hr : π^(q-t) ∣ x := by simp [Nat.sub_eq_zero_of_le hq]
    have hl : π^q ∣ π^t*x := dvd_trans (pow_dvd_pow _ hq) (dvd_mul_right _ _)
    exact iff_of_true hl hr

def powerCyclicLift (π : R) (q t : ℕ) : R →ₗ[R] Cyclic π q :=
  (powAction π t (Cyclic π q)).comp ((PowIdeal π q : Submodule R R).mkQ)

theorem powerCyclicLift_ker (π : R) (hπ : π ≠ 0) (q t : ℕ) :
    LinearMap.ker (powerCyclicLift π q t) = (PowIdeal π (q-t) : Submodule R R) := by
  ext x
  rw [LinearMap.mem_ker]
  change (π^t) • (Ideal.Quotient.mk (PowIdeal π q) x) = 0 ↔ x ∈ PowIdeal π (q-t)
  rw [Algebra.smul_def,Ideal.Quotient.algebraMap_eq,← map_mul,
    Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton,Ideal.mem_span_singleton]
  exact pow_dvd_pow_mul_iff π hπ q t x

omit [IsDomain R] in
theorem powerCyclicLift_range (π : R) (q t : ℕ) :
    LinearMap.range (powerCyclicLift π q t) = PowerImage π t (Cyclic π q) := by
  rw [powerCyclicLift,LinearMap.range_comp,LinearMap.range_eq_top.2 (Submodule.mkQ_surjective _),
    Submodule.map_top]

noncomputable def powerCyclicEquiv (π : R) (hπ : π ≠ 0) (q t : ℕ) :
    Cyclic π (q-t) ≃ₗ[R] PowerImage π t (Cyclic π q) := by
  change (R ⧸ (PowIdeal π (q-t):Submodule R R)) ≃ₗ[R] PowerImage π t (Cyclic π q)
  rw [←powerCyclicLift_ker π hπ q t,←powerCyclicLift_range π q t]
  exact (powerCyclicLift π q t).quotKerEquivRange


omit [IsDomain R] in
theorem maximal_cyclic_length (π : R) (hmax : (Ideal.span ({π}:Set R)).IsMaximal) :
    Module.length R (Cyclic π 1) = 1 := by
  apply Module.length_eq_one_iff.mpr
  have h : (PowIdeal π 1).IsMaximal := by
    change (Ideal.span ({π^1}:Set R)).IsMaximal
    rwa [pow_one]
  exact isSimpleModule_iff_quot_maximal.mpr ⟨_,h,⟨LinearEquiv.refl R _⟩⟩

omit [IsDomain R] in
theorem more_ideal_le (π : R) (s : ℕ) : PowIdeal π (s+1) ≤ PowIdeal π 1 :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.succ_le_succ (Nat.zero_le s)))

def cyclicToSimple (π : R) (s : ℕ) : Cyclic π (s+1) →ₗ[R] Cyclic π 1 :=
  Submodule.factor (more_ideal_le π s)

omit [IsDomain R] in
theorem cyclicToSimple_surjective (π : R) (s : ℕ) :
    Function.Surjective (cyclicToSimple π s) :=
  Submodule.factor_surjective (more_ideal_le π s)

omit [IsDomain R] in
theorem cyclicToSimple_ker (π : R) (s : ℕ) :
    LinearMap.ker (cyclicToSimple π s) = PowerImage π 1 (Cyclic π (s+1)) := by
  ext z
  refine Submodule.Quotient.induction_on _ z ?_
  intro x
  rw [LinearMap.mem_ker]
  have hd : cyclicToSimple π s ((PowIdeal π (s+1):Submodule R R).mkQ x) = 0 ↔ π ∣ x := by
    rw [cyclicToSimple,Submodule.factor_mk]
    change Ideal.Quotient.mk (PowIdeal π 1) x = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton,pow_one]
  change cyclicToSimple π s ((PowIdeal π (s+1):Submodule R R).mkQ x) = 0 ↔ _
  rw [hd]
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨Ideal.Quotient.mk (PowIdeal π (s+1)) y,?_⟩
    rw [powAction_apply,pow_one,Algebra.smul_def,Ideal.Quotient.algebraMap_eq,←map_mul]
    rfl
  · rintro ⟨w,hw⟩
    change powAction π 1 (Cyclic π (s+1)) w = (PowIdeal π (s+1):Submodule R R).mkQ x at hw
    apply hd.mp
    rw [←hw,powAction_apply,pow_one,map_smul,Algebra.smul_def,Ideal.Quotient.algebraMap_eq]
    have hp : Ideal.Quotient.mk (PowIdeal π 1) π = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton,pow_one]
    rw [hp,zero_mul]

theorem cyclic_length (π : R) (hπ : π ≠ 0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (s : ℕ) : Module.length R (Cyclic π s) = s := by
  induction s with
  | zero =>
    haveI : Subsingleton (Cyclic π 0) := by
      have htop : PowIdeal π 0 = (⊤:Ideal R) := by
        change Ideal.span ({π^0}:Set R) = ⊤
        rw [pow_zero,Ideal.span_singleton_one]
      change Subsingleton (R ⧸ PowIdeal π 0)
      rw [htop]
      infer_instance
    exact Module.length_eq_zero
  | succ s ih =>
    have had := Module.length_eq_add_of_exact (LinearMap.ker (cyclicToSimple π s)).subtype
      (cyclicToSimple π s) (Submodule.subtype_injective _) (cyclicToSimple_surjective π s)
      (LinearMap.exact_subtype_ker_map _)
    rw [cyclicToSimple_ker] at had
    rw [had,← (powerCyclicEquiv π hπ (s+1) 1).length_eq]
    simp [maximal_cyclic_length π hmax,ih]

theorem powerCyclic_length (π : R) (hπ : π ≠ 0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (q t : ℕ) : Module.length R (PowerImage π t (Cyclic π q)) = (q-t:ℕ) := by
  rw [← (powerCyclicEquiv π hπ q t).length_eq,cyclic_length π hπ hmax]

#print axioms maximal_cyclic_length
#print axioms cyclicToSimple_ker
#print axioms cyclic_length
#print axioms pow_dvd_pow_mul_iff
#print axioms powerCyclicLift_ker
#print axioms powerCyclicLift_range
#print axioms powerCyclicEquiv
#print axioms powerCyclic_length
end Paper5
