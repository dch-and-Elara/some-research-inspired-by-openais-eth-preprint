import V8PooledMenuSlots

set_option autoImplicit false
set_option warningAsError true

namespace V8NativeMessage
open scoped Classical BigOperators
open MvPolynomial

/-- Multiplicity of one Boolean form never increases the product of
its powers. A witness exponent must actually be positive. -/
theorem powers_same_binary {ι R : Type*} [CommRing R]
    (s : Finset ι) (val : ι→R) (β : ι→ℕ) (m : ι) (hm : m∈s) (hmβ : β m≠0)
    (h : ∀ n∈s, β n≠0 → val n=val m) (hbin : val m=0 ∨ val m=1) :
    (∏ n∈s, val n ^ β n)=val m := by
  rcases hbin with he | he
  · rw [he]
    exact Finset.prod_eq_zero hm (by rw [he,zero_pow hmβ])
  · rw [he]
    apply Finset.prod_eq_one
    intro n hn
    by_cases hb : β n=0
    · rw [hb,pow_zero]
    · rw [h n hn hb,he,one_pow]

theorem filtered_zero {M : Type*} (β : M→₀ℕ) (pred : M→Prop) [DecidablePred pred]
    (h : ∀ m, pred m → β m=0) : β.filter pred=0 := by
  ext m
  by_cases hm : pred m <;> simp [hm,h]

theorem filtered_nonzero {M : Type*} (β : M→₀ℕ) (pred : M→Prop) [DecidablePred pred]
    (m : M) (hm : pred m) (hmβ : β m≠0) : β.filter pred≠0 := by
  intro h
  have e := congrArg (fun w : M→₀ℕ => w m) h
  exact hmβ (by simpa [hm] using e)

theorem packet_factor {G K M P R : Type*} [CommRing R] [DecidableEq G] [DecidableEq K]
    [Fintype M] [DecidableEq M] (target source : M→G×K) (g : G) (k : K) (ports : Finset P)
    (b : P→Bool) (base : P→R) (moment : M→R) (β : M→₀ℕ)
    (ht : ∀ m, target m=(g,k) → β m=0) :
    J6RecursiveModes.packet target source g k ports b base (fun _ _ => 0) moment β =
      (∏ r∈ports, LiteralPortCompiler.affine (b r) (base r)) *
      ∏ m∈Finset.univ.filter (fun m => source m=(g,k)), moment m ^ β m := by
  classical
  have ht' : β.filter (fun m => target m=(g,k))=0 := filtered_zero β _ ht
  simp [J6RecursiveModes.packet,ht',J6RecursiveModes.row_zero,← map_prod, coeff_C]

#print axioms powers_same_binary
#print axioms filtered_zero
#print axioms filtered_nonzero
#print axioms packet_factor
end V8NativeMessage