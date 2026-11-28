import V8NativeMessageC3D

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

/-! Canonical and separate lifts in the literal source rings.
The difference is divisible by the full creation precision, even
though the canonical section is not a ring homomorphism. -/
namespace V8NativeMessage.C3.Canonical
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Integral J6R10Repack
noncomputable section

variable {G : Type*} [Fintype G]

theorem canonical_prod_difference (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ℓ : ℕ)
    (received : G → Box f ℓ p) (separate : G → IntRing f ℓ)
    (hs : ∀ g, reduce p f ℓ (separate g)=received g) :
    (2:IntRing f ℓ)^p ∣ canonicalLift p f hf ℓ (∏ g, received g) - ∏ g, separate g := by
  apply (reduce_zero_iff p f hf ℓ _).mp
  simp only [map_sub,canonicalLift_spec,map_prod,hs,sub_self]

/-- A finite, valuation-free formulation of the multiplier's exact
integrality budget. It covers the same scalar shift as p+v₂(b)≥q
when the source valuation is defined, without assuming a value for zero. -/
def ShiftedIntegral (f : ℤ[X]) (ℓ p q : ℕ) (b : RatRing f ℓ) : Prop :=
  ∃ a : IntRing f ℓ, b*(2:RatRing f ℓ)^p = (2:RatRing f ℓ)^q * embed f ℓ a

/-- The denominator budget of one possibly fractional multiplier. -/
def HasLoss (f : ℤ[X]) (ℓ loss : ℕ) (b : RatRing f ℓ) : Prop :=
  ∃ a : IntRing f ℓ, (2:RatRing f ℓ)^loss*b = embed f ℓ a

omit [Fintype G] in
theorem loss_mul {f : ℤ[X]} {ℓ a b : ℕ} {x y : RatRing f ℓ}
    (hx : HasLoss f ℓ a x) (hy : HasLoss f ℓ b y) : HasLoss f ℓ (a+b) (x*y) := by
  obtain ⟨u,hu⟩ := hx
  obtain ⟨v,hv⟩ := hy
  refine ⟨u*v,?_⟩
  rw [map_mul,← hu,← hv,pow_add]
  ring

omit [Fintype G] in
theorem loss_suffices {f : ℤ[X]} {ℓ p q d : ℕ} {x : RatRing f ℓ}
    (hx : HasLoss f ℓ d x) (fit : q+d≤p) : ShiftedIntegral f ℓ p q x := by
  obtain ⟨u,hu⟩ := hx
  let k : ℕ := p-(q+d)
  have hp : p=q+k+d := by dsimp [k]; omega
  refine ⟨(2:IntRing f ℓ)^k*u,?_⟩
  simp only [map_mul,map_pow,map_ofNat]
  calc
    _ = (2:RatRing f ℓ)^q * ((2:RatRing f ℓ)^k * ((2:RatRing f ℓ)^d*x)) := by
      conv_lhs => rw [hp,pow_add,pow_add]
      ring
    _ = _ := by rw [hu]

omit [Fintype G] in
theorem multiply_difference {f : ℤ[X]} {ℓ p q : ℕ}
    (b : RatRing f ℓ) (fit : ShiftedIntegral f ℓ p q b)
    (x y : IntRing f ℓ) (same : (2:IntRing f ℓ)^p ∣ x-y) :
    ∃ z : IntRing f ℓ, b * (embed f ℓ x - embed f ℓ y) =
      embed f ℓ ((2:IntRing f ℓ)^q*z) := by
  obtain ⟨a,ha⟩ := fit
  obtain ⟨v,hv⟩ := same
  refine ⟨a*v,?_⟩
  rw [← map_sub,hv,map_mul,map_pow,map_ofNat,← mul_assoc,ha,map_mul,map_pow,map_ofNat,map_mul]
  ring

theorem actual_separate_transfer (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ℓ q : ℕ)
    (received : G → Box f ℓ p) (separate : G → IntRing f ℓ)
    (hs : ∀ g, reduce p f ℓ (separate g)=received g)
    (b : RatRing f ℓ) (hb : ShiftedIntegral f ℓ p q b) :
    ∃ z : IntRing f ℓ,
      b * (embed f ℓ (canonicalLift p f hf ℓ (∏ g, received g)) -
           embed f ℓ (∏ g, separate g)) = embed f ℓ ((2:IntRing f ℓ)^q*z) :=
  multiply_difference b hb _ _ (canonical_prod_difference p f hf ℓ received separate hs)

#print axioms canonical_prod_difference
#print axioms loss_mul
#print axioms loss_suffices
#print axioms multiply_difference
#print axioms actual_separate_transfer
end
end V8NativeMessage.C3.Canonical