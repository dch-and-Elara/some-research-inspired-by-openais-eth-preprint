import DenominatorBudget
import NativeProbeRing
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! Canonical reduction of the actual two-local coefficient ring. No map
from the whole rational field to a finite characteristic ring is used. -/
namespace J6ZeroTransport

open scoped BigOperators
open DenominatorBudget

variable {S T : Type*} [CommRing S] [CommRing T]

/-- The finite reciprocal for an odd integer uses p terms in a ring where
2^p=0: if d=1+2k it is the geometric sum of -2k. -/
def oddReciprocal (S : Type*) [CommRing S] (p : ℕ) (d : ℤ) : S :=
  ∑ j ∈ Finset.range p, (-((2:S)*((d/2:ℤ):S)))^j

theorem oddReciprocal_valid (p : ℕ) (h : (2:S)^p=0) (d : ℤ)
    (odd : ¬ (2:ℤ) ∣ d) : (d:S) * oddReciprocal S p d = 1 := by
  let k := d/2
  let x : S := -((2:S)*(k:S))
  have hd : d=2*k+1 := by
    dsimp [k]
    omega
  have hodd : (d:S)=1-x := by
    simp only [x,sub_neg_eq_add]
    rw [hd]
    push_cast
    ring
  have hnil : x^p=0 := by
    change (-((2:S)*(k:S)))^p=0
    rw [neg_pow,mul_pow,h,zero_mul,mul_zero]
  change (d:S) * (∑ j∈Finset.range p,x^j) = 1
  rw [hodd,mul_comm,geom_sum_mul_neg,hnil,sub_zero]

theorem oddCast_unit (p : ℕ) (h : (2:S)^p=0) (d : ℤ) (odd : ¬(2:ℤ)∣d) :
    IsUnit (d:S) :=
  isUnit_of_mul_eq_one _ _ (oddReciprocal_valid p h d odd)

local instance : IsLocalization atTwoPrime.primeCompl TwoLocal := by
  unfold TwoLocal twoLocalSubalgebra
  infer_instance

private theorem odd_of_mem (d : atTwoPrime.primeCompl) : ¬(2:ℤ)∣(d:ℤ) := by
  simpa only [atTwoPrime,Ideal.mem_primeCompl_iff,Ideal.mem_span_singleton] using d.prop

/-- Actual universal homomorphism from the odd-denominator localization. -/
noncomputable def reduceAt (p : ℕ) (h : (2:S)^p=0) : TwoLocal →+* S :=
  IsLocalization.lift (M:=atTwoPrime.primeCompl) (g:=Int.castRingHom S)
    (fun d => oddCast_unit p h d (odd_of_mem d))

theorem reduceAt_int (p : ℕ) (h : (2:S)^p=0) (n : ℤ) :
    reduceAt p h (n:TwoLocal) = (n:S) := by
  unfold reduceAt
  exact IsLocalization.lift_eq _ n

/-- Ring maps on the source odd localization are determined by the integer
subring; in particular they commute across receiving-ring reductions. -/
theorem ringHom_unique (f g : TwoLocal →+* S) : f=g := by
  apply IsLocalization.ringHom_ext atTwoPrime.primeCompl
  ext n
  simp

theorem reduceAt_comp (f : S →+* T) (p q : ℕ) (hp : (2:S)^p=0) (hq : (2:T)^q=0) :
    f.comp (reduceAt p hp) = reduceAt q hq :=
  ringHom_unique _ _

/-- A genuinely odd denominator commutes with reduction via the explicit
finite geometric inverse. Nonunit raw denominators are not inverted here. -/
theorem reduce_fraction (p : ℕ) (h : (2:S)^p=0) (x : TwoLocal) (n d : ℤ)
    (odd : ¬(2:ℤ)∣d) (hx : twoLocalRat x=(n:ℚ)/(d:ℚ)) :
    reduceAt p h x = (n:S)*oddReciprocal S p d := by
  have hd : d≠0 := fun hg => odd (hg ▸ dvd_zero (2:ℤ))
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  have he : (d:TwoLocal)*x = (n:TwoLocal) := by
    apply twoLocalRat_injective
    rw [map_mul,map_intCast,map_intCast,hx,mul_comm,div_mul_cancel₀ _ hd']
  have hz := congrArg (reduceAt p h) he
  rw [map_mul,reduceAt_int,reduceAt_int] at hz
  calc
    _ = reduceAt p h x * ((d:S)*oddReciprocal S p d) := by
      rw [oddReciprocal_valid p h d odd,mul_one]
    _ = ((d:S)*reduceAt p h x)*oddReciprocal S p d := by ac_rfl
    _ = _ := by rw [hz]

noncomputable def reduceBase (p : ℕ) : TwoLocal →+* NativeProbeRing.Base p :=
  reduceAt p (NativeProbeRing.base_nilpotent p)

/-- Receiving ring with the exact lifted, monic binary-coordinate modulus. -/
noncomputable def reduceNative (p : ℕ) (f : Polynomial ℤ) :
    TwoLocal →+* NativeProbeRing.Scalar p f :=
  (AdjoinRoot.of (NativeProbeRing.liftPoly p f)).comp (reduceBase p)

theorem reduceNative_eq (p : ℕ) (f : Polynomial ℤ) :
    reduceNative p f = reduceAt p (NativeProbeRing.scalar_nilpotent p f) :=
  ringHom_unique _ _

theorem base_precision (p q : ℕ) (h : p≤q) :
    (NativeProbeRing.reduceBase p q h).comp (reduceBase q) = reduceBase p :=
  ringHom_unique _ _

theorem native_precision (p q : ℕ) (h : p≤q) (f : Polynomial ℤ) :
    (NativeProbeRing.reduceScalar p q h f).comp (reduceNative q f) = reduceNative p f :=
  ringHom_unique _ _

/-- At ell=1 the additional source jet variable is exactly zero, and its
base embedding followed by the canonical quotient is the same scalar map. -/
theorem truncate_one_base (p : ℕ) (f : Polynomial ℤ) (x : TwoLocal) :
    NativeProbeRing.truncateOne (NativeProbeRing.Scalar p f)
      (AdjoinRoot.of (Polynomial.X : Polynomial (NativeProbeRing.Scalar p f))
        (reduceNative p f x)) = reduceNative p f x :=
  (NativeProbeRing.truncateOne _).apply_symm_apply _

#print axioms oddReciprocal_valid
#print axioms reduceAt_int
#print axioms ringHom_unique
#print axioms reduceAt_comp
#print axioms reduce_fraction
#print axioms reduceNative_eq
#print axioms base_precision
#print axioms native_precision
#print axioms truncate_one_base

end J6ZeroTransport