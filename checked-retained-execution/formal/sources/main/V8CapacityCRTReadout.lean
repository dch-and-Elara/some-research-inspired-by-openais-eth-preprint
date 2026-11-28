import V8CapacityCRTJet

/-! Actual coefficient receipt for v8 A1. CRT remains in the raw integral
source jet until its top coefficient is reduced. The later division by
π^L and Smith saturation are not claimed here. -/
namespace V8CapacityCRTJet
open scoped Polynomial
open Polynomial

noncomputable section

variable (O : Type*) [CommRing O]

def coefficient (k j : ℕ) (u : Jet O k) : O :=
  (AdjoinRoot.modByMonicHom (monic_X.pow k) u).coeff j

theorem source_reduce_mk (π : O) (P k : ℕ) (g : O[X]) :
    reduceJet O π P k (AdjoinRoot.mk ((X:O[X])^k) g) =
      AdjoinRoot.mk ((X:(BaseMod O π P)[X])^k) (g.map (coeffMod O π P)) := by
  rw [reduceJet,AdjoinRoot.lift_mk,integralCoeff,← Polynomial.eval₂_map]
  exact AdjoinRoot.aeval_eq _

theorem coefficient_reduce (π : O) (P k j : ℕ) (u : Jet O k) :
    coefficient (BaseMod O π P) k j (reduceJet O π P k u) =
      coeffMod O π P (coefficient O k j u) := by
  obtain ⟨g,rfl⟩ := AdjoinRoot.mk_surjective u
  rw [source_reduce_mk]
  simp only [coefficient,AdjoinRoot.modByMonicHom_mk]
  have h := Polynomial.map_modByMonic (coeffMod O π P) ((monic_X (R:=O)).pow k) (p:=g)
  rw [Polynomial.map_pow,Polynomial.map_X] at h
  rw [← h,Polynomial.coeff_map]

variable [IsLocalRing O] {H : Type*} [Fintype H] [Fintype (IsLocalRing.ResidueField O)]
local notation "R" => IsLocalRing.ResidueField O

/-- The exact top Taylor coefficient functions in v8, on every constant
residue fiber, form the product of the separately realizable raw columns
modulo π^P. Each local expression may use the full integral truncated
coefficient ring, not merely constant scalars. -/
theorem native_top_raw_columns (π : O) (P k : ℕ)
    (d : R → O) (hd : Function.RightInverse d (IsLocalRing.residue O))
    (goal : (H → R) → (H → ℕ → O) → BaseMod O π P) :
    (∃ C : MvPolynomial H (Jet O k), ∀ a c,
      coefficient (BaseMod O π P) k (k-1)
        (MvPolynomial.eval₂Hom (reduceJet O π P k) (digitInput O π P k d a c) C)=goal a c) ↔
    (∀ a, ∃ C : MvPolynomial H (Jet O k), ∀ c,
      coefficient (BaseMod O π P) k (k-1)
        (MvPolynomial.eval₂Hom (reduceJet O π P k) (digitInput O π P k d a c) C)=goal a c) :=
  native_raw_columns O π P k d hd (coefficient (BaseMod O π P) k (k-1)) goal

#print axioms source_reduce_mk
#print axioms coefficient_reduce
#print axioms native_top_raw_columns
end
end V8CapacityCRTJet
