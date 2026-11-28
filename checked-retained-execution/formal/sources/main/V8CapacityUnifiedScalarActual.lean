import V8CapacityUnifiedWidth
import Mathlib.Algebra.MvPolynomial.Eval

/-! S4 on an arbitrary actual finite set of scalar message tuples.
No injectivity is used in the quotient-width computation; injective
tuples imply the separate full raw ambient rank assertion. -/
namespace V8CapacityUnified.Scalar
open scoped Classical BigOperators
open MvPolynomial V8CapacityCRTJet V8CapacitySmith Module
open V8CapacityUnified V8CapacityWidthUpper

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {O H Z : Type*} [CommRing O] [IsDomain O] [Fintype Z]
variable (u : Z → H → O)

def evaluation : MvPolynomial H O →ₗ[O] (Z → O) where
  toFun A z := MvPolynomial.eval (u z) A
  map_add' _ _ := by funext z; simp
  map_smul' _ _ := by funext z; simp [MvPolynomial.smul_eq_C_mul,smul_eq_mul]

abbrev scalarImage := LinearMap.range (evaluation u)

theorem evaluation_exact_range :
    Set.range (fun A : MvPolynomial H O => fun z => MvPolynomial.eval (u z) A)=↑(scalarImage u) :=
  rfl

variable (inj : Function.Injective u)

include inj in
theorem differing (x : Z) (y : {z : Z // z≠x}) : ∃ i, u x i≠u y.val i := by
  by_contra! h
  exact y.property ((inj (funext h)).symm)

def coordinateAt (x : Z) (y : {z : Z // z≠x}) : H :=
  Classical.choose (differing u inj x y)

theorem coordinateAt_ne (x : Z) (y : {z : Z // z≠x}) :
    u x (coordinateAt u inj x y)≠u y.val (coordinateAt u inj x y) :=
  Classical.choose_spec (differing u inj x y)

def pointIndicator (x : Z) : MvPolynomial H O :=
  ∏ y : {z : Z // z≠x}, (X (coordinateAt u inj x y)-C (u y.val (coordinateAt u inj x y)))

def pointWeight (x : Z) : O := MvPolynomial.eval (u x) (pointIndicator u inj x)

theorem pointWeight_ne (x : Z) : pointWeight u inj x≠0 := by
  simp only [pointWeight,pointIndicator,map_prod,map_sub,MvPolynomial.eval_X,MvPolynomial.eval_C]
  refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
  exact sub_ne_zero.mpr (coordinateAt_ne u inj x j)

theorem point_off (x y : Z) (h : y≠x) :
    MvPolynomial.eval (u y) (pointIndicator u inj x)=0 := by
  simp only [pointIndicator,map_prod,map_sub,MvPolynomial.eval_X,MvPolynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨y,h⟩:{z : Z // z≠x})) (sub_self _)

def commonWeight : O := ∏ z : Z, pointWeight u inj z

theorem commonWeight_ne : commonWeight u inj≠0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun z _ => pointWeight_ne u inj z)

/-- Integral delta products yield a nonzero full-rank lattice even
where the scalar evaluation module is not saturated. -/
theorem scalar_lattice_contains (v : Z → O) : (commonWeight u inj) • v∈scalarImage u := by
  let cofactor (z : Z) := ∏ r ∈ Finset.univ.erase z, pointWeight u inj r
  refine ⟨∑ z : Z, C (cofactor z*v z)*pointIndicator u inj z,?_⟩
  funext x
  change (eval (u x)) (∑ z : Z, C (cofactor z*v z)*pointIndicator u inj z) =
    commonWeight u inj*v x
  simp only [map_sum,map_mul,MvPolynomial.eval_C]
  rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
  · change cofactor x*v x*pointWeight u inj x=commonWeight u inj*v x
    have h : pointWeight u inj x*cofactor x=commonWeight u inj :=
      Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)
    rw [← h]
    ring
  · intro z _ hz
    rw [point_off u inj z x (Ne.symm hz),mul_zero]

variable [IsLocalRing O] [IsPrincipalIdealRing O] {π : O}
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))

local notation "S₀" => U2_chart π hMax (scalarImage u)
local notation "S" => (S₀).2

include hMax inj in
theorem scalar_smith_no_outside : Function.Surjective (S).chart.f := by
  intro z
  by_contra hz
  have hm := scalar_lattice_contains u inj ((S).chart.bM z)
  have hzero := ((exact_membership S _).mp hm).2 z hz
  simp [coord] at hzero
  exact commonWeight_ne u inj hzero

include inj in
theorem scalar_smith_full_ambient : (S₀).1=Fintype.card Z := by
  have he := Fintype.card_congr (Equiv.ofBijective (S).chart.f
    ⟨(S).chart.f.injective,scalar_smith_no_outside u inj hMax⟩)
  simpa using he

variable (L p : ℕ)

def S4_observation_exact (hπ : π≠0) :
    ((i : Fin (S₀).1) → BaseMod O π (p-((S).exponent i-L))) ≃ₗ[O]
      attainable π L p (scalarImage u) :=
  U5_module p S hπ L

theorem S4_width_witness (hπ : π≠0) (hp : 0<p) :
    ∃ recv : Active S (L+p) → MvPolynomial H O, ∃ v : Active S (L+p) → Z → O,
      (∀ y z, π^(L+p)∣MvPolynomial.eval (u z) (recv y)-π^L*v y z) ∧
      IsLeast {d : ℕ | factors π p (fun y => residueRows π p (v y)) d}
        (Fintype.card (Active S (L+p))) :=
  U_width_real_receivers p S L hπ hp hMax _ (evaluation_exact_range u)

#print axioms evaluation_exact_range
#print axioms coordinateAt_ne
#print axioms pointWeight_ne
#print axioms scalar_lattice_contains
#print axioms scalar_smith_no_outside
#print axioms scalar_smith_full_ambient
#print axioms S4_observation_exact
#print axioms S4_width_witness
end
end V8CapacityUnified.Scalar
