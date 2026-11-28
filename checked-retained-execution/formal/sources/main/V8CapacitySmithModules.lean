import V8CapacitySmithSaturation
import Mathlib.LinearAlgebra.Pi

/-! A4's observable module is the product of cyclic quotient modules.
The coordinates are actual Smith coordinates of an image submodule;
errors in the ambient module encode congruence, not free image vectors. -/
namespace V8CapacitySmith
open scoped Classical BigOperators
open Module V8CapacityCyclic V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false

variable {O M I : Type*} [CommRing O] [IsDomain O]
variable [AddCommGroup M] [Module O M] [Fintype I]
variable {π : O} {N : Submodule O M} {n : ℕ}
variable (S : Powered π N I n) (L p : ℕ)

def clipped (i : Fin n) : ℕ := min p (S.exponent i-L)

def component (i : Fin n) : Submodule O (BaseMod O π p) :=
  LinearMap.range (mulReduce O π p (clipped S L p i))

def observed : Submodule O (Fin n → BaseMod O π p) :=
  Submodule.pi Set.univ (component S L p)

theorem readable_obs (hπ : π≠0) (v : Fin n → BaseMod O π p) :
    v∈observed S L p ↔ ∃ x : M, realizable π L p N x ∧
      ∀ i : Fin n, coeffMod O π p (coord S x (S.chart.f i))=v i := by
  rw [observed,Submodule.mem_pi]
  constructor
  · intro hv
    have hV (i : Fin n) : ∃ c : O, mulReduce O π p (clipped S L p i) c=v i :=
      hv i (Set.mem_univ i)
    choose c hc using hV
    let a (j : I) : O :=
      if h : j∈Set.range S.chart.f then
        π^(clipped S L p (Classical.choose h))*c (Classical.choose h) else 0
    let x := fromCoord S a
    have ha (i : Fin n) : coord S x (S.chart.f i) = π^(clipped S L p i)*c i := by
      rw [show coord S x (S.chart.f i)=a (S.chart.f i) from coord_fromCoord S a _]
      have hh : S.chart.f i∈Set.range S.chart.f := ⟨i,rfl⟩
      have he : Classical.choose hh=i := S.chart.f.injective (Classical.choose_spec hh)
      simp only [a,dif_pos hh,he]
    refine ⟨x,(exact_saturation S hπ L p x).mpr ⟨?_,?_⟩,fun i => ?_⟩
    · intro i
      rw [ha]
      exact dvd_mul_right _ _
    · intro j hj
      rw [show coord S x j=a j from coord_fromCoord S a _]
      unfold a
      rw [dif_neg hj]
      exact dvd_zero _
    · rw [ha]
      exact hc i
  · rintro ⟨x,hSat,hV⟩ i _
    obtain ⟨c,hc⟩ := ((exact_saturation S hπ L p x).mp hSat).1 i
    refine ⟨c,?_⟩
    change coeffMod O π p (π^(min p (S.exponent i-L))*c)=v i
    rw [← hc,hV]

theorem outside_read_zero (hπ : π≠0) (x : M) (hx : realizable π L p N x)
    (j : I) (hj : j∉Set.range S.chart.f) : coeffMod O π p (coord S x j)=0 := by
  obtain ⟨e,he⟩ := ((exact_saturation S hπ L p x).mp hx).2 j hj
  have hz : coeffMod O π p (π^p)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [he,map_mul,hz,zero_mul]

def rangePiIso : ((i : Fin n) → component S L p i) ≃ₗ[O] observed S L p where
  toFun x := ⟨fun i => (x i).val,Submodule.mem_pi.mpr (fun i _ => (x i).property)⟩
  invFun x := fun i => ⟨x.val i,Submodule.mem_pi.mp x.property i (Set.mem_univ i)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Finite-product form of A4. The factor at d≥L+p is the quotient by
π^0, hence a zero module; at d<L+p the exponent is p-(d-L)_+. -/
def A4_modules (hπ : π≠0) :
    ((i : Fin n) → BaseMod O π (p-clipped S L p i)) ≃ₗ[O] observed S L p :=
  (LinearEquiv.piCongrRight (fun i =>
    cyclicIso O π hπ p (clipped S L p i) (min_le_left _ _))).trans (rangePiIso S L p)

theorem active_module_exponent (i : Fin n) (h : S.exponent i<L+p) :
    p-clipped S L p i=p-(S.exponent i-L) := by
  unfold clipped
  rw [min_eq_right (by omega)]

theorem inactive_module_zero (i : Fin n) (h : L+p≤S.exponent i) (x : BaseMod O π (p-clipped S L p i)) :
    x=0 := by
  obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective x
  have he : p-clipped S L p i=0 := by unfold clipped; omega
  change Ideal.Quotient.mk (Ideal.span ({π^(p-clipped S L p i)}:Set O)) u=0
  rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton,he,pow_zero]
  exact one_dvd _

#print axioms readable_obs
#print axioms outside_read_zero
#print axioms A4_modules
#print axioms active_module_exponent
#print axioms inactive_module_zero
end
end V8CapacitySmith
