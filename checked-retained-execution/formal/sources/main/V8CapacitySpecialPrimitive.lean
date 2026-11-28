import V8CapacitySpecialSignatures

/-! Choose the exact least coefficient valuation of each native active
column, and divide by its power of the uniformizer in the polynomial
ring itself. Distinct columns still cannot share a monomial pivot. -/
namespace V8CapacitySpecialPrimitive
open scoped Polynomial Classical BigOperators
open V8CapacityNativeMatrix V8CapacitySymbolic V8CapacitySpecialSignatures
open V8CapacitySmith

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000

variable {O E H : Type*} [CommRing O] [IsDomain O]

def hasBreak (π : O) (f : MvPolynomial E O) (s : ℕ) : Prop :=
  ∃ d : E →₀ ℕ, ¬π^(s+1)∣f.coeff d

theorem some_break (π : O) (P : ℕ) (f : MvPolynomial E O)
    (hf : ∃ d, ¬π^P∣f.coeff d) : ∃ s, hasBreak π f s := by
  have hP : 0<P := by
    by_contra! hn
    obtain ⟨d,hd⟩ := hf
    rw [show P=0 by omega,pow_zero] at hd
    exact hd (one_dvd _)
  exact ⟨P-1,by simpa [hasBreak,show P-1+1=P by omega] using hf⟩

def μ (π : O) (P : ℕ) (f : MvPolynomial E O) (hf : ∃ d, ¬π^P∣f.coeff d) : ℕ :=
  Nat.find (some_break π P f hf)

theorem mu_break (π : O) (P : ℕ) (f : MvPolynomial E O) (hf : ∃ d, ¬π^P∣f.coeff d) :
    hasBreak π f (μ π P f hf) :=
  Nat.find_spec (some_break π P f hf)

theorem mu_lt (π : O) (P : ℕ) (f : MvPolynomial E O) (hf : ∃ d, ¬π^P∣f.coeff d) :
    μ π P f hf<P := by
  have hP : 0<P := by
    by_contra! hn
    obtain ⟨d,hd⟩ := hf
    rw [show P=0 by omega,pow_zero] at hd
    exact hd (one_dvd _)
  have h : hasBreak π f (P-1) := by simpa [hasBreak,show P-1+1=P by omega] using hf
  have hu := Nat.find_min' (some_break π P f hf) h
  change μ π P f hf ≤ P-1 at hu
  omega

theorem mu_is_minimum (π : O) (P : ℕ) (f : MvPolynomial E O) (hf : ∃ d, ¬π^P∣f.coeff d) (s : ℕ) :
    (∀ d, π^s∣f.coeff d) ↔ s≤μ π P f hf := by
  constructor
  · intro hall
    by_contra! hs
    obtain ⟨d,hd⟩ := mu_break π P f hf
    exact hd ((pow_dvd_pow π (by omega)).trans (hall d))
  · intro hs d
    cases s with
    | zero => simp
    | succ s =>
      by_contra h
      have hn : s<μ π P f hf := by omega
      exact (Nat.find_min (some_break π P f hf) hn) ⟨d,h⟩

theorem polynomial_homogeneous_divisor (u : O) (f : MvPolynomial E O)
    (hall : ∀ d, u∣f.coeff d) : ∃ g : MvPolynomial E O, f=MvPolynomial.C u*g := by
  choose c hc using hall
  refine ⟨∑ d ∈ f.support, MvPolynomial.monomial d (c d),?_⟩
  rw [Finset.mul_sum]
  simp_rw [MvPolynomial.C_mul_monomial,← hc]
  exact MvPolynomial.as_sum f

theorem support_primitive_eq (u : O) (hu : u≠0) (f g : MvPolynomial E O)
    (h : f=MvPolynomial.C u*g) : f.support=g.support := by
  ext a
  rw [MvPolynomial.mem_support_iff,MvPolynomial.mem_support_iff,h,MvPolynomial.coeff_C_mul]
  exact mul_ne_zero_iff_left hu

variable [IsLocalRing O] [Fintype H]

structure Primitive (π : O) (P : ℕ) (f : MvPolynomial E O)
    (hf : ∃ d, ¬π^P∣f.coeff d) where
  poly : MvPolynomial E O
  pivot : E →₀ ℕ
  factor : f=MvPolynomial.C (π^μ π P f hf)*poly
  unit : Oˣ
  hit : poly.coeff pivot=(unit:O)

def normalize (π : O) (P : ℕ) (f : MvPolynomial E O)
    (hf : ∃ d, ¬π^P∣f.coeff d)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) :
    Primitive π P f hf := by
  let hgExists := polynomial_homogeneous_divisor (π^μ π P f hf) f
    ((mu_is_minimum π P f hf _).mpr le_rfl)
  let g := Classical.choose hgExists
  have hg : f=MvPolynomial.C (π^μ π P f hf)*g := Classical.choose_spec hgExists
  let d := Classical.choose (mu_break π P f hf)
  have hd : ¬π^(μ π P f hf+1)∣f.coeff d := Classical.choose_spec (mu_break π P f hf)
  have hU : IsUnit (g.coeff d) := by
    apply (IsLocalRing.notMem_maximalIdeal).mp
    intro hm
    rw [hMax,Ideal.mem_span_singleton] at hm
    obtain ⟨x,hx⟩ := hm
    apply hd
    have hgf := congrArg (MvPolynomial.coeff d) hg
    rw [MvPolynomial.coeff_C_mul] at hgf
    rw [hgf,hx,pow_succ,← mul_assoc]
    exact dvd_mul_right _ _
  exact ⟨g,d,hg,hU.unit,hU.unit_spec.symm⟩

def colμ (π : O) (P k : ℕ) (i : Columns H π P k) : ℕ :=
  μ π P (symCol π P k i.val) i.property

def primitiveCol (π : O) (P k : ℕ)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) (i : Columns H π P k) :
    Primitive π P (symCol π P k i.val) i.property :=
  normalize π P (symCol π P k i.val) i.property hMax

theorem chosen_low (π : O) (P k : ℕ) (i : Columns H π P k) : colμ π P k i<P :=
  mu_lt π P (symCol π P k i.val) i.property

theorem primitive_degree (π : O) (P k : ℕ) (hπ : π≠0)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) (i : Columns H π P k) :
    (primitiveCol π P k hMax i).poly.totalDegree≤DegreeCap P k := by
  let g := primitiveCol π P k hMax i
  have h := support_primitive_eq _ (pow_ne_zero _ hπ) _ _ g.factor
  change g.poly.support.sup (fun m : Digits H k →₀ ℕ => m.sum fun _ e => e)≤_
  rw [← h]
  exact symCol_degree π P k i.val

theorem primitive_orthogonal (π : O) (P k : ℕ) (hk : 0<k)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (i j : Columns H π P k) (hπ : π≠0) (hij : i≠j) :
    (primitiveCol π P k hMax j).poly.coeff (primitiveCol π P k hMax i).pivot=0 := by
  let g := primitiveCol π P k hMax i
  let f := primitiveCol π P k hMax j
  have hi : (symCol π P k i.val).coeff g.pivot≠0 := by
    have he := congrArg (MvPolynomial.coeff g.pivot) g.factor
    rw [he,MvPolynomial.coeff_C_mul,g.hit]
    exact mul_ne_zero (pow_ne_zero _ hπ) g.unit.ne_zero
  by_contra hn
  have hj : (symCol π P k j.val).coeff g.pivot≠0 := by
    have he := congrArg (MvPolynomial.coeff g.pivot) f.factor
    rw [he,MvPolynomial.coeff_C_mul]
    exact mul_ne_zero (pow_ne_zero _ hπ) hn
  exact hij (Subtype.ext (actual_cols_disjoint π P k hk i.val j.val g.pivot hi hj))

#print axioms mu_lt
#print axioms mu_is_minimum
#print axioms polynomial_homogeneous_divisor
#print axioms support_primitive_eq
#print axioms normalize
#print axioms primitive_degree
#print axioms primitive_orthogonal
end
end V8CapacitySpecialPrimitive

