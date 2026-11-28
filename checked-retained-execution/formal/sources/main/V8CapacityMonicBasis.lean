import V8CapacitySymbolic
import V8CapacityNewtonGrid

/-! The monic tensor Newton basis really spans every polynomial of the
specified total degree. Newton coefficients are not external data. -/
namespace V8CapacityMonicBasis
open scoped Classical BigOperators
open V8CapacityDigits V8CapacityFactorial V8CapacityNewtonGrid
open MvPolynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {O E : Type*} [CommRing O] [Fintype E]
variable {π : O} {q : ℕ} (D : Digits π q) (hq : 0<q)

def basisPoly (a : E → ℕ) : MvPolynomial E O :=
  ∏ e : E, ∏ i ∈ Finset.range (a e), (X e-C (node D hq i))

def bump (a : E → ℕ) (e : E) : E → ℕ := fun j => a j+(if j=e then 1 else 0)

theorem bump_weight (a : E → ℕ) (e : E) : ∑ j : E, bump a e j = (∑ j : E, a j)+1 := by
  simp [bump,Finset.sum_add_distrib]

theorem basis_inc (a : E → ℕ) (e : E) :
    basisPoly D hq (bump a e)=(X e-C (node D hq (a e)))*basisPoly D hq a := by
  unfold basisPoly
  let f (j : E) := ∏ i ∈ Finset.range (a j), (X j-C (node D hq i))
  let g (j : E) := ∏ i ∈ Finset.range (bump a e j), (X j-C (node D hq i))
  change (∏ j : E, g j)=(X e-C (node D hq (a e)))*∏ j : E, f j
  rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ e),
    ← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ e)]
  have h_rest : ∏ j ∈ Finset.univ.erase e, g j = ∏ j ∈ Finset.univ.erase e, f j := by
    apply Finset.prod_congr rfl
    intro j hj
    have h : j≠e := Finset.ne_of_mem_erase hj
    simp [f,g,bump,h]
  have h_here : g e=f e*(X e-C (node D hq (a e))) := by
    simp [g,f,bump,Finset.prod_range_succ]
  rw [h_rest,h_here]
  ac_rfl

def possible (n : ℕ) : Set (MvPolynomial E O) :=
  {p | ∃ a : E → ℕ, (∑ e : E, a e)≤n ∧ basisPoly D hq a=p}

def spanMonic (n : ℕ) : Submodule O (MvPolynomial E O) :=
  Submodule.span O (possible D hq n)

theorem basis_in (a : E → ℕ) (n : ℕ) (h : (∑ e : E, a e)≤n) :
    basisPoly D hq a∈spanMonic D hq n :=
  Submodule.subset_span ⟨a,h,rfl⟩

theorem span_mono {n m : ℕ} (h : n≤m) : spanMonic D hq n≤spanMonic (E:=E) D hq m := by
  apply Submodule.span_mono
  rintro _ ⟨a,ha,rfl⟩
  exact ⟨a,ha.trans h,rfl⟩

theorem span_one : (1:MvPolynomial E O)∈spanMonic D hq 0 := by
  convert basis_in D hq (0:E→ℕ) 0 (by simp) using 1
  simp [basisPoly]

theorem span_X {n : ℕ} (e : E) (p : MvPolynomial E O)
    (hp : p∈spanMonic D hq n) : p*X e∈spanMonic D hq (n+1) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a,ha,rfl⟩ := hp
    have h : basisPoly D hq a*X e =
        basisPoly D hq (bump a e)+node D hq (a e) • basisPoly D hq a := by
      rw [basis_inc,MvPolynomial.smul_eq_C_mul]
      ring
    rw [h]
    apply Submodule.add_mem
    · apply basis_in
      rw [bump_weight]
      omega
    · apply Submodule.smul_mem
      exact basis_in D hq a _ (by omega)
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ hx

theorem span_X_pow {n : ℕ} (e : E) (p : MvPolynomial E O)
    (hp : p∈spanMonic D hq n) (a : ℕ) : p*X e^a∈spanMonic D hq (n+a) := by
  induction a with
  | zero => simpa using hp
  | succ a ih =>
    rw [pow_succ,← mul_assoc,Nat.add_succ]
    exact span_X D hq e _ ih

theorem span_X_prod (s : Finset E) (a : E → ℕ) :
    (∏ e ∈ s, X e^a e : MvPolynomial E O)∈spanMonic D hq (∑ e ∈ s, a e) := by
  induction s using Finset.induction_on with
  | empty => simpa using span_one (E:=E) D hq
  | @insert e s he ih =>
    rw [Finset.prod_insert he,Finset.sum_insert he,add_comm (a e),mul_comm]
    exact span_X_pow D hq e _ ih _

theorem span_monomial (n : ℕ) (a : E →₀ ℕ) (w : O) (ha : ∑ e : E, a e≤n) :
    monomial a w∈spanMonic D hq n := by
  rw [MvPolynomial.monomial_eq,← MvPolynomial.smul_eq_C_mul,Finsupp.prod_pow]
  exact (spanMonic D hq n).smul_mem w (span_mono D hq ha (span_X_prod D hq Finset.univ a))

theorem bounded_polynomial_in_span (n : ℕ) (p : MvPolynomial E O) (hd : p.totalDegree≤n) :
    p∈spanMonic D hq n := by
  rw [p.as_sum]
  apply Submodule.sum_mem
  intro a ha
  apply span_monomial D hq
  have hh := (MvPolynomial.le_totalDegree ha).trans hd
  rw [Finsupp.sum_fintype _ (fun (_ : E) (i : ℕ) => i) (fun _ => rfl)] at hh
  exact hh

abbrev Row (E : Type*) [Fintype E] (n : ℕ) :=
  { a : E → Fin (n+1) // (∑ e : E, (a e).val)≤n }

def rowDegree {n : ℕ} (a : Row E n) (e : E) : ℕ := (a.val e).val

theorem finite_row_range (n : ℕ) :
    Set.range (fun a : Row E n => basisPoly D hq (rowDegree a))=possible D hq n := by
  ext p
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨rowDegree a,a.property,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    have h (i : E) : a i<n+1 := by
      have h₁ : a i ≤ ∑ e : E, a e :=
        Finset.single_le_sum (f:=a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    let b : Row E n := ⟨fun i => ⟨a i,h i⟩,ha⟩
    exact ⟨b,rfl⟩

theorem exact_monic_expansion (n : ℕ) (p : MvPolynomial E O) (hd : p.totalDegree≤n) :
    ∃ a : Row E n → O, ∑ i : Row E n, a i • basisPoly D hq (rowDegree i)=p := by
  apply (Submodule.mem_span_range_iff_exists_fun O).mp
  rw [finite_row_range]
  exact bounded_polynomial_in_span D hq n p hd

theorem basis_eval (a : E → ℕ) (x : E → O) :
    MvPolynomial.eval x (basisPoly D hq a) =
      ∏ e : E, ∏ r ∈ Finset.range (a e), (x e-node D hq r) := by
  simp only [basisPoly,map_prod,map_sub,MvPolynomial.eval_X,MvPolynomial.eval_C]

#print axioms basis_inc
#print axioms bounded_polynomial_in_span
#print axioms finite_row_range
#print axioms exact_monic_expansion
#print axioms basis_eval
end
end V8CapacityMonicBasis

