import V8NativeMessageC3HermiteCarrier

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4100000

/-! The actual MAIN Hermite node contribution and its ordinary orbit
loss. The exactness lemma compares with the unique interpolant's
constant coefficient (the row evaluated by the source determinant). -/
namespace V8NativeMessage.C3.Hermite
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6ActiveUniqueness J6ActiveHermite
noncomputable section

def extraLoss (Q J : ℕ) : ℕ := (J-1)*logLoss Q

def nodeReadout (Q J v : ℕ) (jet : ℚ[X]) : ℚ :=
  (carrier Q J v).eval 0 * (trim J (jet*invLocal Q J v)).eval (-(v:ℚ))

theorem integer_local (z : ℤ) : (z:ℚ)∈twoLocalSubalgebra :=
  (mem_twoLocal_iff _).mpr ⟨z,1,by decide,by simp⟩

theorem two_pow_local (n : ℕ) : (2:ℚ)^n∈twoLocalSubalgebra :=
  twoLocalSubalgebra.pow_mem (by exact integer_local 2) n

theorem trim_coeff_low (J : ℕ) (p : ℚ[X]) (k : ℕ) (h : k<J) :
    (trim J p).coeff k=p.coeff k := by
  symm
  simpa only [coeff_sub,sub_eq_zero] using (X_pow_dvd_iff.mp (prefix_dvd J p)) k h

theorem trim_eval_range {J : ℕ} (hJ : 0<J) (p : ℚ[X]) (x : ℚ) :
    (trim J p).eval x=∑ k∈Finset.range J,p.coeff k*x^k := by
  have hn : (X:ℚ[X])^J ≠ 1 := by
    intro H
    have he := congrArg Polynomial.natDegree H
    simp at he
    omega
  have hd : (trim J p).natDegree < J := by
    unfold trim
    simpa using natDegree_modByMonic_lt p (monic_X.pow J) hn
  rw [eval_eq_sum_range' hd x]
  exact Finset.sum_congr rfl (fun k hk => by rw [trim_coeff_low J p k (Finset.mem_range.mp hk)])

theorem scaled_node_product_coeff {Q J v m k : ℕ}
    (hv : v∈nodes Q) (hk : k<J) (jet : ℚ[X])
    (hi : ∀ r<J, (2:ℚ)^m * jet.coeff r ∈ twoLocalSubalgebra) :
    (2:ℚ)^(m+extraLoss Q J) * (jet*invLocal Q J v).coeff k ∈twoLocalSubalgebra := by
  rw [coeff_mul,Finset.mul_sum]
  refine twoLocalSubalgebra.sum_mem (fun rs hrs => ?_)
  have hsum : rs.1+rs.2=k := by simpa using hrs
  have h₁ : rs.1<J := by omega
  have h₂ : rs.2≤J-1 := by omega
  have hE : logLoss Q*rs.2≤extraLoss Q J := by
    rw [extraLoss,mul_comm (J-1)]
    exact Nat.mul_le_mul_left _ h₂
  let d := extraLoss Q J-logLoss Q*rs.2
  have he : m+extraLoss Q J=m+logLoss Q*rs.2+d := by dsimp [d]; omega
  rw [he]
  have hprod :
      (2:ℚ)^(m+logLoss Q*rs.2+d)*(jet.coeff rs.1*(invLocal Q J v).coeff rs.2) =
      (((2:ℚ)^m*jet.coeff rs.1) *
        ((2:ℚ)^(logLoss Q*rs.2)*(invLocal Q J v).coeff rs.2))* (2:ℚ)^d := by
    rw [pow_add,pow_add]
    ring
  rw [hprod]
  exact twoLocalSubalgebra.mul_mem
    (twoLocalSubalgebra.mul_mem (hi rs.1 h₁) (invLocal_coeff_loss J rs.2 hv))
    (two_pow_local d)

theorem node_readout_loss {Q J v m : ℕ} (hv : v∈nodes Q) (hJ : 0<J) (jet : ℚ[X])
    (hi : ∀ r<J, (2:ℚ)^m*jet.coeff r∈twoLocalSubalgebra) :
    (2:ℚ)^(m+extraLoss Q J)*nodeReadout Q J v jet ∈twoLocalSubalgebra := by
  unfold nodeReadout
  rw [show (2:ℚ)^(m+extraLoss Q J) *
       ((carrier Q J v).eval 0 * (trim J (jet*invLocal Q J v)).eval (-(v:ℚ))) =
       (carrier Q J v).eval 0 *
       ((2:ℚ)^(m+extraLoss Q J)*(trim J (jet*invLocal Q J v)).eval (-(v:ℚ))) by ring]
  refine twoLocalSubalgebra.mul_mem (origin_carrier_integral J hv) ?_
  rw [trim_eval_range hJ,Finset.mul_sum]
  refine twoLocalSubalgebra.sum_mem (fun k hk => ?_)
  rw [← mul_assoc]
  have hneg : (-(v:ℚ))∈twoLocalSubalgebra := by exact_mod_cast integer_local (-(v:ℤ))
  exact twoLocalSubalgebra.mul_mem
    (scaled_node_product_coeff hv (Finset.mem_range.mp hk) jet hi)
    (twoLocalSubalgebra.pow_mem hneg k)

theorem native_origin_weight_loss {Q J v : ℕ} (hv : v∈nodes Q) (hJ : 0<J) (j : ℕ) :
    (2:ℚ)^extraLoss Q J * nodeReadout Q J v ((X:ℚ[X])^j) ∈twoLocalSubalgebra := by
  have hi : ∀ r<J, (2:ℚ)^0*((X:ℚ[X])^j).coeff r∈twoLocalSubalgebra := by
    intro r _
    simp only [pow_zero,one_mul,coeff_X_pow]
    split <;> simp
  simpa only [Nat.zero_add] using node_readout_loss hv hJ _ hi

theorem printed_origin_exact {Q J : ℕ} (hJ : 0<J) (f : ℚ[X]) (hdeg : f.natDegree<Q*J)
    (sample : ℕ→ℚ[X])
    (hs : ∀ v∈nodes Q, ∀ j<J,(sample v).coeff j=(atNode (1:ℚˣ) (v:ℚ) f).coeff j) :
    (∑ v∈nodes Q,nodeReadout Q J v (sample v))=f.eval 0 := by
  have hsum : (∑ v∈nodes Q,J)=Q*J := by
    simp [nodes,Nat.card_Icc]
  have he := recover_at (nodes Q) (fun i => (i:ℚ)) (fun _ => J) invDiff
    (1:ℚˣ) f sample 0 (fun _ _ => hJ)
    (fun _ _ w hw => invDiff_mul (Finset.mem_erase.mp hw).1.symm)
    (by simpa only [hsum] using hdeg) hs
  simpa only [nodeReadout,carrier,dividedJet,invLocal,normalized,inv_one,Units.val_one,
    one_mul,zero_sub] using he

#print axioms trim_coeff_low
#print axioms trim_eval_range
#print axioms scaled_node_product_coeff
#print axioms node_readout_loss
#print axioms native_origin_weight_loss
#print axioms printed_origin_exact
end
end V8NativeMessage.C3.Hermite