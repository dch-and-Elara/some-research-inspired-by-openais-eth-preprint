import P5CyclicLength
import Mathlib.LinearAlgebra.Quotient.Pi

/-! The two natural maps on powers and quotients, and their effect on
actual Mathlib module length. In particular the quotient of a free
module by a scalar power is a product of honest cyclic quotients. -/
namespace Paper5
open scoped BigOperators

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem map_mem_power (π : R) (t : ℕ) (f : M →ₗ[R] N) {x : M}
    (hx : x ∈ PowerImage π t M) : f x ∈ PowerImage π t N := by
  obtain ⟨a,rfl⟩ := hx
  refine ⟨f a,?_⟩
  simp

def powImageMap (π : R) (t : ℕ) (f : M →ₗ[R] N) :
    PowerImage π t M →ₗ[R] PowerImage π t N :=
  (f.comp (PowerImage π t M).subtype).codRestrict _ (fun x => map_mem_power π t f x.property)

theorem powImageMap_surjective (π : R) (t : ℕ) (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (powImageMap π t f) := by
  intro y
  obtain ⟨b,hb⟩ := y.property
  obtain ⟨a,ha⟩ := hf b
  refine ⟨⟨powAction π t M a,⟨a,rfl⟩⟩,Subtype.ext ?_⟩
  change f (powAction π t M a) = y.val
  rw [← hb,powAction_apply,powAction_apply,map_smul,ha]

abbrev PowerQuot (π : R) (t : ℕ) (M : Type*) [AddCommGroup M] [Module R M] :=
  M ⧸ PowerImage π t M

def powQuotMap (π : R) (t : ℕ) (f : M →ₗ[R] N) :
    PowerQuot π t M →ₗ[R] PowerQuot π t N :=
  (PowerImage π t M).mapQ (PowerImage π t N) f (fun _ hx => map_mem_power π t f hx)

theorem powQuotMap_surjective (π : R) (t : ℕ) (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (powQuotMap π t f) := by
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro y
  obtain ⟨x,hx⟩ := hf y
  exact ⟨(PowerImage π t M).mkQ x,by simp [powQuotMap,Submodule.mapQ_apply,hx]⟩

theorem length_power_exact (π : R) (t : ℕ) :
    Module.length R M = Module.length R (PowerImage π t M) +
      Module.length R (PowerQuot π t M) :=
  Module.length_eq_add_of_exact (PowerImage π t M).subtype (PowerImage π t M).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)

variable {I : Type*}

theorem powerImage_pi (π : R) (t : ℕ) (V : I → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] :
    PowerImage π t (∀ i, V i) = Submodule.pi Set.univ (fun i => PowerImage π t (V i)) := by
  classical
  ext x
  rw [Submodule.mem_pi]
  constructor
  · rintro ⟨y,rfl⟩ i _
    exact ⟨y i,rfl⟩
  · intro h
    choose y hy using fun i => h i (Set.mem_univ i)
    exact ⟨y,funext hy⟩

noncomputable def piPowerEquiv (π : R) (t : ℕ) (V : I → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] :
    PowerImage π t (∀ i, V i) ≃ₗ[R] ∀ i, PowerImage π t (V i) where
  toFun x i := ⟨x.val i,by
    obtain ⟨a,ha⟩ := x.property
    exact ⟨a i,congrFun ha i⟩⟩
  invFun x := ⟨fun i => (x i).val,by
    rw [powerImage_pi π t V,Submodule.mem_pi]
    exact fun i _ => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem powerImage_ring (π : R) (t : ℕ) :
    PowerImage π t R = (PowIdeal π t : Submodule R R) := by
  ext x
  change (∃ a : R, π^t*a=x) ↔ x ∈ PowIdeal π t
  rw [Ideal.mem_span_singleton]
  exact ⟨fun ⟨a,h⟩ => ⟨a,h.symm⟩,fun ⟨a,h⟩ => ⟨a,h.symm⟩⟩

noncomputable def powerQuotFreeEquiv [Fintype I] [DecidableEq I] (π : R) (t : ℕ) :
    PowerQuot π t (I → R) ≃ₗ[R] (I → Cyclic π t) := by
  change ((I → R) ⧸ PowerImage π t (I → R)) ≃ₗ[R] (I → Cyclic π t)
  rw [powerImage_pi,powerImage_ring]
  exact Submodule.quotientPi _

variable [IsDomain R]

theorem powerQuotFree_length [Fintype I] [DecidableEq I] (π : R) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (t : ℕ) :
    Module.length R (PowerQuot π t (I → R)) = (Fintype.card I * t : ℕ) := by
  rw [(powerQuotFreeEquiv (I:=I) π t).length_eq,Module.length_pi_of_fintype]
  simp [cyclic_length π hπ hmax]

theorem powerImageCyclicGrid_length [Fintype I] (π : R) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (ex : I → ℕ) (t : ℕ) :
    Module.length R (PowerImage π t (∀ i, Cyclic π (ex i))) =
      (∑ i, (ex i-t:ℕ) : ℕ) := by
  rw [(piPowerEquiv π t (fun i => Cyclic π (ex i))).length_eq,Module.length_pi_of_fintype]
  simp [powerCyclic_length π hπ hmax]

#print axioms powImageMap_surjective
#print axioms powQuotMap_surjective
#print axioms length_power_exact
#print axioms powerImage_pi
#print axioms piPowerEquiv
#print axioms powerQuotFreeEquiv
#print axioms powerQuotFree_length
#print axioms powerImageCyclicGrid_length
end Paper5
