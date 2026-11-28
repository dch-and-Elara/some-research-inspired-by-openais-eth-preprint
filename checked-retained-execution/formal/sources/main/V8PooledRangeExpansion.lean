import V8PooledRangeClusters

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace V8PooledRange
namespace Split

theorem cluster_old_endpoint {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) (e : E) (b : Bool) :
    clusterOf k (graph H p (.inr (.inl e)) b) = H e b := by
  rw [old_endpoint]
  cases coreHalf (sourceIndex H p e b) <;> rfl

private theorem lost_old_cross {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) (f : V k → Bool)
    (e : Cross H (representative f))
    (hc : f (graph H p (.inr (.inl e.val)) false) = f (graph H p (.inr (.inl e.val)) true)) :
    Partial f (H e.val false) ∨ Partial f (H e.val true) := by
  by_contra h
  have hd := not_or.mp h
  have he (b : Bool) (hne : ¬Partial f (H e.val b)) :
      f (graph H p (.inr (.inl e.val)) b) = representative f (H e.val b) := by
    by_contra hmiss
    exact hne ⟨_,cluster_old_endpoint H p e.val b,hmiss⟩
  exact e.property ((he false hd.1).symm.trans (hc.trans (he true hd.2)))

private noncomputable def boundaryCode {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) (f : V k → Bool)
    (e : Cross H (representative f)) :
    Cross (graph H p) f ⊕ (PartialClusters f × Fin 3) := by
  classical
  by_cases hc : f (graph H p (.inr (.inl e.val)) false) = f (graph H p (.inr (.inl e.val)) true)
  · by_cases h0 : Partial f (H e.val false)
    · exact .inr (⟨H e.val false,h0⟩,sourceIndex H p e.val false)
    · have h1 := (lost_old_cross H p f e hc).resolve_left h0
      exact .inr (⟨H e.val true,h1⟩,sourceIndex H p e.val true)
  · exact .inl ⟨.inr (.inl e.val),hc⟩

private def boundaryDecode {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) (f : V k → Bool) :
    Cross (graph H p) f ⊕ (PartialClusters f × Fin 3) → Edges k E
  | .inl e => e.val
  | .inr q => .inr (.inl ((p q.1.val).symm q.2).val.1)

private theorem boundary_code_decode {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) (f : V k → Bool)
    (e : Cross H (representative f)) :
    boundaryDecode H p f (boundaryCode H p f e) = .inr (.inl e.val) := by
  unfold boundaryCode
  split
  · split <;> simp only [boundaryDecode,sourceIndex,Equiv.symm_apply_apply]
  · rfl

/-- Removed old edges can be charged to an actual incidence at a partial
cluster, so there are at most three charges per partial cluster. -/
theorem old_boundary_compare {k : ℕ} {E : Type*} [Fintype E]
    (H : Graph (Deficit k) E) (p : ThreePorts H) (f : V k → Bool) :
    Fintype.card (Cross H (representative f)) ≤
      Fintype.card (Cross (graph H p) f) + 3*Fintype.card (PartialClusters f) := by
  have hn := Fintype.card_le_of_injective (boundaryCode H p f) (by
    intro a b h
    have hp := congrArg (boundaryDecode H p f) h
    rw [boundary_code_decode,boundary_code_decode] at hp
    exact Subtype.ext (Sum.inl.inj (Sum.inr.inj hp)))
  rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] at hn
  exact hn

def Expansion {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (γ : ℚ) : Prop :=
  ∀ f : V → Bool,
    γ * ((min (Fintype.card (Part f false)) (Fintype.card (Part f true)) : ℕ) : ℚ) ≤
      (Fintype.card (Cross G f) : ℚ)

private theorem minimum_card_bound (x₀ x₁ y₀ y₁ b : ℕ)
    (h₀ : x₀ ≤ (y₀+b)*4) (h₁ : x₁ ≤ (y₁+b)*4) :
    min x₀ x₁ ≤ (min y₀ y₁+b)*4 := by
  rcases le_total y₀ y₁ with h | h
  · rw [min_eq_left h]
    exact (min_le_left x₀ x₁).trans h₀
  · rw [min_eq_right h]
    exact (min_le_right x₀ x₁).trans h₁

/-- The exact loss from the C5 split-core completion. The proof uses the
actual distinct cluster seats and actual crossing edges, not an expansion
assumption about the completed graph. -/
theorem expansion {k : ℕ} {E : Type*} [Fintype E]
    (H : Graph (Deficit k) E) (p : ThreePorts H)
    (γ : ℚ) (hγ : 0 ≤ γ) (hH : Expansion H γ) :
    Expansion (graph H p) (γ / (4*(γ+4))) := by
  intro f
  let x : ℕ := min (Fintype.card (Part f false)) (Fintype.card (Part f true))
  let y : ℕ := min (Fintype.card (Part (representative f) false))
    (Fintype.card (Part (representative f) true))
  let b : ℕ := Fintype.card (PartialClusters f)
  let m : ℕ := Fintype.card (Cross H (representative f))
  let c : ℕ := Fintype.card (Cross (graph H p) f)
  have hx : x ≤ (y+b)*4 := minimum_card_bound _ _ _ _ _ (side_card_bound f false) (side_card_bound f true)
  have hb : b ≤ c := partial_card_bound H p f
  have hm : m ≤ c + 3*b := old_boundary_compare H p f
  have he : γ * (y : ℚ) ≤ (m : ℚ) := hH (representative f)
  have hx' : (x : ℚ) ≤ ((y : ℚ)+(b : ℚ))*4 := by exact_mod_cast hx
  have hb' : (b : ℚ) ≤ (c : ℚ) := by exact_mod_cast hb
  have hm' : (m : ℚ) ≤ (c : ℚ)+3*(b : ℚ) := by exact_mod_cast hm
  have hp : 0 < 4*(γ+4) := by linarith
  change γ/(4*(γ+4))*(x : ℚ) ≤ (c : ℚ)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).mpr
  have hgx := mul_le_mul_of_nonneg_left hx' hγ
  have hgb := mul_le_mul_of_nonneg_left hb' hγ
  nlinarith

#print axioms cluster_old_endpoint
#print axioms old_boundary_compare
#print axioms expansion

end Split
end V8PooledRange
