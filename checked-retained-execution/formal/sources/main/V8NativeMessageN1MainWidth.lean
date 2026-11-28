import V8NativeMessageN1MainHeight

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

/-! A closed parameter-dependent binary width for the actual MAIN N1
coefficient ledger. Does not turn an arithmetic upper bound into an
acquisition lower bound or assert a cost for generating the layout. -/
namespace V8NativeMessage.N1
open scoped Classical BigOperators Polynomial
open V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

def bits (a : ℕ) : ℕ := Nat.log 2 a+1

theorem fits_bits (a : ℕ) : a<2^bits a :=
  Nat.lt_pow_succ_log_self (by decide) a

theorem δ_factorial_bound (R Q : ℕ) (hRQ : R≤Q) : δ R Q≤(Q+1)^(2*Q) := by
  have hf : Q.factorial≤(Q+1)^Q :=
    (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left (Nat.le_succ _) _)
  unfold δ
  have hr : (R-1).factorial≤Q.factorial := Nat.factorial_le ((Nat.sub_le _ _).trans hRQ)
  rw [two_mul,pow_add]
  exact Nat.mul_le_mul (hr.trans hf) hf

def denomExp (Q : ℕ) : ℕ := bits (Q+1)*(2*Q)
def evalExp (n R Q BP : ℕ) : ℕ := bits n+bits (R+1)+BP+bits (Q+1)*R
def atomicExp (n R Q BP : ℕ) : ℕ := max (denomExp Q) (2+evalExp n R Q BP)+2

theorem δ_denom_exp (R Q : ℕ) (hRQ : R≤Q) : δ R Q≤2^denomExp Q := by
  unfold denomExp
  rw [pow_mul]
  exact (δ_factorial_bound R Q hRQ).trans (Nat.pow_le_pow_left (fits_bits _).le _)

variable (W : Type*) [Fintype W]

theorem evaluation_exponential (R Q BP : ℕ) :
    oneEval W R Q BP≤2^evalExp (Fintype.card (Clone W)) R Q BP := by
  unfold oneEval evalExp
  rw [pow_add,pow_add,pow_add,pow_mul]
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul (Nat.mul_le_mul (fits_bits _).le (fits_bits _).le) (le_refl _)
  · exact Nat.pow_le_pow_left (fits_bits _).le _

theorem atomic_exp_valid (R Q BP : ℕ) (hRQ : R≤Q) :
    A W R Q BP≤2^atomicExp (Fintype.card (Clone W)) R Q BP := by
  let e := evalExp (Fintype.card (Clone W)) R Q BP
  let u := max (denomExp Q) (2+e)
  have hδ : δ R Q≤2^u := (δ_denom_exp R Q hRQ).trans
    (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have he : 3*oneEval W R Q BP≤2^(2+e) := by
    rw [pow_add]
    exact Nat.mul_le_mul (by decide) (evaluation_exponential W R Q BP)
  have h3 : 3*oneEval W R Q BP≤2^u := he.trans
    (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  change 2*(δ R Q+3*oneEval W R Q BP)≤2^(u+2)
  calc
    _ ≤ 2*(2^u+2^u) := Nat.mul_le_mul_left _ (Nat.add_le_add hδ h3)
    _ = _ := by rw [pow_add]; ring

variable {W} [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}
variable (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
variable {R BP : ℕ} (H : RowBound L hreg R BP)

include H in
theorem partial_explicit_width (hRQ : R≤Q) (s : W→Bool) (h : feasible L.frame)
    (G : Finset (Fin r)) (xs : ∀ g, Finset (Word L.frame g)) (j : Fin J) :
    within (roomAt L G+atomicExp (Fintype.card (Clone W)) R Q BP*degreeAt L G+1)
      (jetCoeff J j (ratPartial L hreg s h G xs)) := by
  obtain ⟨hD,hN⟩ := partial_rational_height L hreg H s h G xs j
  exact bits_of_bounds (δ_pos _ _) (δ_le_base (W:=W))
    (atomic_exp_valid W R Q BP hRQ) hD hN

include H in
theorem completed_explicit_width (hRQ : R≤Q) (s : W→Bool) (h : feasible L.frame)
    (j : Fin J) :
    within (4*Fintype.card W+atomicExp (Fintype.card (Clone W)) R Q BP*(12*Fintype.card W)+1)
      (jetCoeff J j (nativeScan F hreg L s).2.2) := by
  obtain ⟨hD,hN⟩ := completed_rational_height L hreg H s h j
  exact bits_of_bounds (δ_pos _ _) (δ_le_base (W:=W))
    (atomic_exp_valid W R Q BP hRQ) hD hN

#print axioms δ_factorial_bound
#print axioms δ_denom_exp
#print axioms evaluation_exponential
#print axioms atomic_exp_valid
#print axioms partial_explicit_width
#print axioms completed_explicit_width
end
end V8NativeMessage.N1
