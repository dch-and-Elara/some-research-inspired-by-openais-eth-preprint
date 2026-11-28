import J6R48BitCostProbe

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

/-! Exact node-load accounting of the genuine Lagrange bit interpreter.
Changing only input-loader fees leaves the computed jet unchanged but
adds one charge per true reread, with no modeled cache. -/
namespace J6R48BitCost
open A1R10 A1R12 AOracleMachineTime J6R22Active J6R24MeteredRecursion

variable {p ell k n : ℕ} {fw : List (Word p)}
variable (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (hk : 0<k)

theorem factor_load_delta (x : UVBlock fw ell)
    {y z : Meter (UVBlock fw ell)} {e : ℕ} (h : Delta y z e) :
    Delta (factorM hp he hv hk x y) (factorM hp he hv hk x z) e := by
  refine ⟨?_,?_⟩
  · simp only [factorM,h.value]
  · simp only [factorM,h.value,h.fee]
    omega

theorem jet_product_load_delta {A : Type*}
    (x y : A → Meter (JetTape fw ell k)) (e : A→ℕ) (xs : List A)
    (matchFee : ∀ a∈xs,Delta (x a) (y a) (e a)) :
    Delta (paidJetProd hp he hv hk x xs) (paidJetProd hp he hv hk y xs) (xs.map e).sum := by
  induction xs with
  | nil => exact Delta.refl _
  | cons a as ih =>
    have H := matchFee a List.mem_cons_self
    have W := ih (fun z hz=>matchFee z (List.mem_cons_of_mem _ hz))
    refine ⟨?_,?_⟩
    · simp only [paidJetProd,H.value,W.value]
    · simp only [paidJetProd,H.value,W.value,H.fee,W.fee,List.map_cons,List.sum_cons]
      omega

theorem basis_load_delta (x y : Fin n→Meter (UVBlock fw ell)) (e : ℕ)
    (same : ∀ i,Delta (x i) (y i) e) (i : Fin n) :
    Delta (basisM hp he hv hk x i) (basisM hp he hv hk y i) (n*e) := by
  have h := same i
  let a := fun j=>factorM hp he hv hk (x i).result (x j)
  let b := fun j=>factorM hp he hv hk (y i).result (y j)
  have z : ∀ j∈offDiagonal i,Delta (a j) (b j) e := by
    intro j _
    change Delta (factorM hp he hv hk (x i).result (x j))
      (factorM hp he hv hk (y i).result (y j)) e
    rw [h.value]
    exact factor_load_delta hp he hv hk (y i).result (same j)
  have q := jet_product_load_delta hp he hv hk a b (fun _=>e) (offDiagonal i) z
  have c := sum_constant_receipts (offDiagonal i) (fun _=>e) e (fun _ _=>rfl)
  rw [offDiagonal_length] at c
  rw [c] at q
  have hn : n-1+1=n := by have := i.isLt; omega
  have hs : n*e=(n-1)*e+e := by
    calc
      _ = (n-1+1)*e := congrArg (·*e) hn.symm
      _ = _ := by rw [Nat.add_mul,Nat.one_mul]
  refine ⟨q.value,?_⟩
  change (x i).steps+(paidJetProd hp he hv hk a (offDiagonal i)).steps+4*(n+1)^2+6 =
    (y i).steps+(paidJetProd hp he hv hk b (offDiagonal i)).steps+4*(n+1)^2+6+n*e
  rw [h.fee,q.fee,hs]
  omega

theorem interpolation_load_delta
    (x y sample : Fin n→Meter (UVBlock fw ell)) (e : ℕ)
    (same : ∀ i,Delta (x i) (y i) e) :
    Delta (interpPrefix hp he hv hk x sample) (interpPrefix hp he hv hk y sample) (n*(n*e)) := by
  have h (i : Fin n) : Delta (interpTerm hp he hv hk x sample i)
      (interpTerm hp he hv hk y sample i) (n*e) := by
    obtain ⟨v,q⟩ := basis_load_delta hp he hv hk x y e same i
    refine ⟨?_,?_⟩
    · simp only [interpTerm,v]
    · simp only [interpTerm,v,q]
      omega
  have H := jet_sum_delta hp he (interpTerm hp he hv hk x sample)
    (interpTerm hp he hv hk y sample) (fun _=>n*e) (probeOrder n) (fun i _=>h i)
  have c := sum_constant_receipts (probeOrder n) (fun _=>n*e) (n*e) (fun _ _=>rfl)
  have hL : (probeOrder n).length=n := List.length_ofFn
  rw [hL] at c
  rw [c] at H
  exact H.pad (4*(n+1)^2+4)

#print axioms factor_load_delta
#print axioms jet_product_load_delta
#print axioms basis_load_delta
#print axioms interpolation_load_delta
end J6R48BitCost

