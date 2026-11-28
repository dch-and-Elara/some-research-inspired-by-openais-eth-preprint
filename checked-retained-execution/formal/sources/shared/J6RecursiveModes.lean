import LiteralPortCompiler
import Mathlib.Tactic

/-! Exact packet/target/source recipe of the printed recursion at
zeta = 0, where literal crossing coefficients vanish. Mode tuples
are exponents, not port allocations. -/
namespace J6RecursiveModes
open scoped BigOperators
open MvPolynomial
variable {R G K M P : Type*} [CommRing R] [DecidableEq G] [DecidableEq K]
  [Fintype M] [DecidableEq M]

noncomputable def row (bit : Bool) (b : R) (cross : M → R) : MvPolynomial M R :=
  C (LiteralPortCompiler.affine bit b) +
    ∑ m, monomial (Finsupp.single m 1) (LiteralPortCompiler.slope bit * cross m)

noncomputable def packet (target source : M → G × K) (g : G) (k : K)
    (ports : Finset P) (bit : P → Bool) (base : P → R)
    (cross : P → M → R) (moment : M → R) (β : M →₀ ℕ) : R :=
  coeff (β.filter (fun m => target m=(g,k)))
    (∏ p ∈ ports, row (bit p) (base p) (cross p)) *
    ∏ m ∈ Finset.univ.filter (fun m => source m=(g,k)), moment m ^ β m

omit [DecidableEq M] in
theorem row_zero (y : Bool) (b : R) :
    row y b (fun _ : M => (0:R)) = C (LiteralPortCompiler.affine y b) := by
  simp [row]

theorem packet_zero_mode (target source : M → G × K) (g : G) (k : K)
    (ports : Finset P) (bit : P → Bool) (base : P → R) (moment : M → R) :
    packet target source g k ports bit base (fun _ _ => 0) moment 0 =
      ∏ p ∈ ports, LiteralPortCompiler.affine (bit p) (base p) := by
  simp only [packet,row_zero,Finsupp.filter_zero,Finsupp.zero_apply,pow_zero,
    Finset.prod_const_one,mul_one,← map_prod,coeff_C]
  simp

theorem packet_positive_target_zero (target source : M → G × K) (g : G) (k : K)
    (ports : Finset P) (bit : P → Bool) (base : P → R)
    (moment : M → R) (β : M →₀ ℕ)
    (h : (β.filter (fun m => target m=(g,k))) ≠ 0) :
    packet target source g k ports bit base (fun _ _ => 0) moment β = 0 := by
  simp only [packet,row_zero,← map_prod,coeff_C,if_neg (Ne.symm h),zero_mul]

variable [Fintype G] [Fintype K] {U : G → Type*} [∀ g, Fintype (U g)]

noncomputable def child
    (target source : M → G × K) (ports : G → K → Finset P)
    (retained : ∀ g, U g → R) (bit : ∀ g, U g → P → Bool)
    (base : ∀ g, U g → P → R) (cross : ∀ g, U g → P → M → R)
    (moment : ∀ g, U g → M → R) (β : M →₀ ℕ) (g : G) : R :=
  ∑ x : U g, retained g x *
    ∏ k, packet target source g k (ports g k) (bit g x) (base g x) (cross g x) (moment g x) β

omit [Fintype G] in
theorem child_zero_mode
    (target source : M → G × K) (ports : G → K → Finset P)
    (retained : ∀ g, U g → R) (bit : ∀ g, U g → P → Bool)
    (base : ∀ g, U g → P → R) (moment : ∀ g, U g → M → R) (g : G) :
    child target source ports retained bit base (fun _ _ _ _ => 0) moment 0 g =
    ∑ x : U g, retained g x * ∏ k, ∏ p ∈ ports g k,
      LiteralPortCompiler.affine (bit g x p) (base g x p) := by
  simp only [child,packet_zero_mode]

theorem offZero_childProduct
    (target source : M → G × K) (ports : G → K → Finset P)
    (retained : ∀ g, U g → R) (bit : ∀ g, U g → P → Bool)
    (base : ∀ g, U g → P → R) (moment : ∀ g, U g → M → R)
    (β : M →₀ ℕ) (hβ : β ≠ 0) :
    (∏ g, child target source ports retained bit base (fun _ _ _ _ => 0) moment β g) = 0 := by
  classical
  have hm : ∃ m, β m ≠ 0 := by
    by_contra! hh
    apply hβ
    ext m
    exact hh m
  obtain ⟨m,hm⟩ := hm
  let g := (target m).1
  let k := (target m).2
  have hmk : target m=(g,k) := Prod.eta _
  have hb : β.filter (fun m => target m=(g,k)) ≠ 0 := by
    intro hf
    have he := congrArg (fun f : M →₀ ℕ => f m) hf
    exact hm (by simpa [hmk] using he)
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  unfold child
  apply Finset.sum_eq_zero
  intro x _
  have hz : (∏ k', packet target source g k' (ports g k') (bit g x) (base g x)
      (fun _ _ => 0) (moment g x) β) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ k)
      (packet_positive_target_zero target source g k _ _ _ _ β hb)
  rw [hz,mul_zero]

/-- Actual source mode summation at the zero probe, independent of how
one enumerates the allowed tuples. The printed weighted menu contains zero. -/
theorem exact_zero_mode_register
    (target source : M → G × K) (ports : G → K → Finset P)
    (retained : ∀ g, U g → R) (bit : ∀ g, U g → P → Bool)
    (base : ∀ g, U g → P → R) (moment : ∀ g, U g → M → R)
    (menu : Finset (M →₀ ℕ)) (hzero : 0 ∈ menu) :
    (∑ β ∈ menu, ∏ g,
      child target source ports retained bit base (fun _ _ _ _ => 0) moment β g) =
    ∏ g, ∑ x : U g, retained g x * ∏ k, ∏ p ∈ ports g k,
      LiteralPortCompiler.affine (bit g x p) (base g x p) := by
  classical
  rw [Finset.sum_eq_single_of_mem 0 hzero]
  · simp only [child_zero_mode]
  · exact fun β _ hβ => offZero_childProduct target source ports retained bit base moment β hβ

#print axioms packet_zero_mode
#print axioms packet_positive_target_zero
#print axioms offZero_childProduct
#print axioms exact_zero_mode_register
end J6RecursiveModes
