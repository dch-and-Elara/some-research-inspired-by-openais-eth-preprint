import J5R41LiteralChildCostWork

/-! The actual pair of outer representatives forces i=0.
The finite exponent estimates do not have a separate oddness input. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open P11FullPacking J6R10Repack J6R9PacketScopes
noncomputable section
set_option linter.unusedSectionVars false

theorem outer_native_valuation {a : ℕ} (i : Fin a) (t : ℤ)
    (outer : t.natAbs=2^a-1) (ht : padicValInt 2 t=i.val) : i.val=0 := by
  rw [←ht,padicValInt,outer]
  apply padicValNat.eq_zero_of_not_dvd
  have ap : 0<a := i.isLt.pos
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ap)
  rw [pow_succ]
  rintro ⟨k,hk⟩
  have h : (0:ℕ)<2^n := by positivity
  omega

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G)

theorem actual_outer_parity_scale (t : ℤ)
    (outer : t.natAbs=2^a-1) (ht : padicValInt 2 t=i.val) :
    ((matched P i g t).card + Fintype.card (Tile P i×Bool))*2^a≤15*Nat.card E :=
  parity_outer_exponent P i g t outer (outer_native_valuation i t outer ht)

variable {p : ℕ} (req : Finset (Mode i p P.mask))

theorem actual_outer_integer_scale (t : ℤ)
    (outer : t.natAbs=2^a-1) (ht : padicValInt 2 t=i.val)
    (bmax : ℕ) (hModes : ∀ m∈req,source P.mask i m=g ∧ m.order.val≤bmax) :
    (2^(matched P i g t).card*V P i req)^(2^a) ≤
      2^(3*Nat.card E)*(tileLen i^(bmax+1)+1)^(6*Nat.card E*(bmax+1)) :=
  bounded_powers_full_outer P i g req t outer (outer_native_valuation i t outer ht) bmax hModes

#print axioms outer_native_valuation
#print axioms actual_outer_parity_scale
#print axioms actual_outer_integer_scale
end
end J5R41LiteralChildCost

