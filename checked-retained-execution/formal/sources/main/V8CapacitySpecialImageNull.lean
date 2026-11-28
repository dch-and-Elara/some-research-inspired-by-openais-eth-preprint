import V8CapacityFeatures

/-! The proper-image specialization uses exact constant coefficients,
not residues: every attained jet has factor z after subtracting its
constant term. The monic null polynomial is common to every row. -/
namespace V8CapacitySpecialImageNull
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityCRTJet V8CapacityFeatures

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 750000

variable {O Z : Type*} [CommRing O] [Fintype Z]
variable {k : ℕ}

theorem subtract_constant (hk : 0<k) (u : Jet O k) :
    ∃ v : Jet O k, u-constJet O k (coefficient O k 0 u)=zJet O k*v := by
  obtain ⟨g,rfl⟩ := AdjoinRoot.mk_surjective u
  rw [coefficient_mk k 0 hk]
  let A := AdjoinRoot.mk ((X:O[X])^k)
  have h := congrArg A (X_mul_divX_add g)
  rw [map_add,map_mul] at h
  refine ⟨A (divX g),?_⟩
  change A g - A (C (g.coeff 0))=A X*A (divX g)
  exact (sub_eq_iff_eq_add.mpr h.symm)

theorem centered_nilpotent (hk : 0<k) (u : Jet O k) :
    (u-constJet O k (coefficient O k 0 u))^k=0 := by
  obtain ⟨v,hv⟩ := subtract_constant hk u
  rw [hv,mul_pow,zJet_nil,zero_mul]

def exactConstants (u : Z → Jet O k) : Finset O :=
  Finset.univ.image (fun z => coefficient O k 0 (u z))

def nullPolynomial (u : Z → Jet O k) : (Jet O k)[X] :=
  ∏ c ∈ exactConstants u, (X-C (constJet O k c))^k

theorem null_vanishes (u : Z → Jet O k) (hk : 0<k) (z : Z) :
    (nullPolynomial u).eval (u z)=0 := by
  unfold nullPolynomial
  rw [← coe_evalRingHom, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩)
  simpa only [coe_evalRingHom,eval_pow,eval_sub,eval_X,eval_C] using (centered_nilpotent hk (u z))

theorem null_monic (u : Z → Jet O k) : (nullPolynomial u).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => (monic_X_sub_C _).pow k)

variable [Nontrivial (Jet O k)]

theorem null_degree (u : Z → Jet O k) :
    (nullPolynomial u).natDegree=(exactConstants u).card*k := by
  unfold nullPolynomial
  rw [natDegree_prod_of_monic (exactConstants u) (fun c => (X-C (constJet O k c))^k)
    (fun _ _ => (monic_X_sub_C _).pow k)]
  calc
    _ = ∑ _c ∈ exactConstants u, k := by
      apply Finset.sum_congr rfl
      intro c _
      rw [(monic_X_sub_C (constJet O k c)).natDegree_pow,natDegree_X_sub_C,mul_one]
    _ = _ := by simp

variable [Nonempty Z]

theorem bound_pos (u : Z → Jet O k) (hk : 0<k) :
    0<(exactConstants u).card*k := by
  apply Nat.mul_pos _ hk
  obtain z := Classical.arbitrary Z
  exact Finset.card_pos.mpr ⟨coefficient O k 0 (u z),
    Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩⟩

/-- Uniform finite exponent reduction on a prescribed finite image,
before any modulo pi truncation and before taking a coefficient. -/
theorem bounded_power (u : Z → Jet O k) (hk : 0<k) (n : ℕ) :
    ∃ a : Fin ((exactConstants u).card*k) → Jet O k,
      ∀ z : Z, (u z)^n=∑ d : Fin ((exactConstants u).card*k), a d*(u z)^d.val := by
  let Q := nullPolynomial u
  let R : (Jet O k)[X] := X^n %ₘ Q
  have hQ : Q.Monic := null_monic u
  have hnd : Q.natDegree=(exactConstants u).card*k := null_degree u
  have hQ' : Q≠1 := by
    intro hn
    have h := congrArg natDegree hn
    rw [natDegree_one,hnd] at h
    exact (Nat.ne_of_gt (bound_pos u hk)) h
  have hR : R.natDegree<(exactConstants u).card*k := by
    rw [← hnd]
    exact natDegree_modByMonic_lt (X^n) hQ hQ'
  refine ⟨fun d => R.coeff d,fun z => ?_⟩
  have he := congrArg (fun f : (Jet O k)[X] => f.eval (u z)) (modByMonic_add_div (X^n) hQ)
  change (R+Q*((X^n)/ₘ Q)).eval (u z)=(X^n).eval (u z) at he
  simp only [eval_add,eval_mul,eval_pow,eval_X] at he
  rw [show Q.eval (u z)=0 from null_vanishes u hk z,zero_mul,add_zero] at he
  rw [← he]
  have hR' := R.as_sum_range_C_mul_X_pow' hR
  conv_lhs => rw [hR']
  simp only [eval_finset_sum,eval_mul,eval_C,eval_pow,eval_X]
  exact (Fin.sum_univ_eq_sum_range (fun x => R.coeff x*(u z)^x) _).symm

#print axioms subtract_constant
#print axioms centered_nilpotent
#print axioms null_vanishes
#print axioms null_degree
#print axioms bounded_power
end
end V8CapacitySpecialImageNull

