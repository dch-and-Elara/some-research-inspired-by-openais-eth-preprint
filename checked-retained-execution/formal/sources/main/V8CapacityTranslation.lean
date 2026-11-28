import V8CapacityCRTReadout
import Mathlib.Algebra.MvPolynomial.Monad

/-! All residue fibers have the same translated digit-column module.
The original integral decoder chart uses actual substitutions, not an
assumed independence of monomial features over the residue field. -/
namespace V8CapacityTranslation
open scoped Classical Polynomial
open V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false

variable {H O S U V : Type*} [CommRing O] [CommRing S]

def translate (c : H → O) : MvPolynomial H O →ₐ[O] MvPolynomial H O :=
  MvPolynomial.bind₁ (fun e => MvPolynomial.X e + MvPolynomial.C (c e))

theorem translate_eval (φ : O →+* S) (x : H → S) (c : H → O) (F : MvPolynomial H O) :
    MvPolynomial.eval₂Hom φ x (translate c F) =
      MvPolynomial.eval₂Hom φ (fun e => x e+φ (c e)) F := by
  simp only [translate,MvPolynomial.eval₂Hom_bind₁,map_add,MvPolynomial.eval₂Hom_X',
    MvPolynomial.eval₂Hom_C]

theorem shifted_range (φ : O →+* S) (c : H → O) (x : U → H → S)
    (read : S → V) (goal : U → V) :
    (∃ F : MvPolynomial H O, ∀ a, read (MvPolynomial.eval₂Hom φ (fun e => x a e+φ (c e)) F)=goal a) ↔
    (∃ F : MvPolynomial H O, ∀ a, read (MvPolynomial.eval₂Hom φ (x a) F)=goal a) := by
  constructor
  · rintro ⟨F,hF⟩
    exact ⟨translate c F,fun a => by rw [translate_eval]; exact hF a⟩
  · rintro ⟨F,hF⟩
    refine ⟨translate (fun e => -c e) F,fun a => ?_⟩
    rw [translate_eval]
    simpa only [map_neg,add_neg_cancel_right] using hF a

variable (O) [IsLocalRing O] [Fintype H] [Fintype (IsLocalRing.ResidueField O)]
local notation "R" => IsLocalRing.ResidueField O

def digitShift (π : O) (P k : ℕ) (c : H → ℕ → O) : H → FiniteJet O π P k :=
  digitInput O π P k (fun _ => 0) (fun _ => 0) c

theorem exact_shift_input (π : O) (P k : ℕ) (d : R → O)
    (a : H → R) (c : H → ℕ → O) (e : H) :
    digitInput O π P k d a c e =
      digitShift O π P k c e + (reduceJet O π P k) (constJet O k (d (a e))) := by
  simp only [digitShift,digitInput,map_zero,zero_add,reduceJet_const]
  exact add_comm _ _

/-- All global raw top-coefficient columns are products of copies of
one and the same actual centered digit family, one copy per residue
word. Any rank or width of that family must still be derived. -/
theorem native_same_centered_columns (π : O) (P k : ℕ)
    (d : R → O) (hd : Function.RightInverse d (IsLocalRing.residue O))
    (goal : (H → R) → (H → ℕ → O) → BaseMod O π P) :
    (∃ F : MvPolynomial H (Jet O k), ∀ a c,
      coefficient (BaseMod O π P) k (k-1)
        (MvPolynomial.eval₂Hom (reduceJet O π P k) (digitInput O π P k d a c) F)=goal a c) ↔
    (∀ a : H → R, ∃ F : MvPolynomial H (Jet O k), ∀ c,
       coefficient (BaseMod O π P) k (k-1)
         (MvPolynomial.eval₂Hom (reduceJet O π P k) (digitShift O π P k c) F)=goal a c) := by
  rw [native_top_raw_columns O π P k d hd goal]
  apply forall_congr'
  intro a
  have hshift (c : H → ℕ → O) : digitInput O π P k d a c =
      fun e => digitShift O π P k c e+(reduceJet O π P k) (constJet O k (d (a e))) :=
    funext (exact_shift_input O π P k d a c)
  simp only [hshift]
  exact shifted_range (reduceJet O π P k) (fun e => constJet O k (d (a e)))
    (digitShift O π P k) (coefficient (BaseMod O π P) k (k-1)) (goal a)

#print axioms translate_eval
#print axioms shifted_range
#print axioms exact_shift_input
#print axioms native_same_centered_columns
end
end V8CapacityTranslation
