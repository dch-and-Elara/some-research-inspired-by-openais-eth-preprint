import V8NativeMessageC3Canonical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace V8NativeMessage.C3.Canonical
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive

noncomputable section
variable {H : Type*} [Fintype H] {f : ℤ[X]} {ℓ q : ℕ}

/-- Signed fixed sums of transfer-certified differences retain exactly
the terminal residue. This does not assert multiplicativity of the
canonical lifting section. -/
theorem assemble_replacements (hf : f.Monic)
    (whole separate : H→RatRing f ℓ) (A : IntRing f ℓ)
    (start : ∑ h, whole h = embed f ℓ A)
    (safe : ∀ h, ∃ v : IntRing f ℓ, whole h-separate h=embed f ℓ ((2:IntRing f ℓ)^q*v)) :
    ∃ B : IntRing f ℓ,
      (∑ h, separate h)=embed f ℓ B ∧ reduce q f ℓ B=reduce q f ℓ A := by
  choose v he using safe
  let e : IntRing f ℓ := (2:IntRing f ℓ)^q * ∑ h, v h
  have hres : reduce q f ℓ e=0 := (reduce_zero_iff q f hf ℓ e).mpr ⟨∑ h, v h,rfl⟩
  have hexact : (∑ h, whole h)-(∑ h, separate h)=embed f ℓ e := by
    dsimp only [e]
    rw [← Finset.sum_sub_distrib,Finset.mul_sum,map_sum]
    exact Finset.sum_congr rfl (fun h _ => he h)
  refine ⟨A-e,?_,?_⟩
  · rw [start] at hexact
    rw [map_sub,← hexact]
    ring
  · rw [map_sub,hres,sub_zero]

theorem shifted_zero (f : ℤ[X]) (ℓ p q : ℕ) : ShiftedIntegral f ℓ p q 0 :=
  ⟨0,by simp⟩

#print axioms assemble_replacements
#print axioms shifted_zero
end
end V8NativeMessage.C3.Canonical