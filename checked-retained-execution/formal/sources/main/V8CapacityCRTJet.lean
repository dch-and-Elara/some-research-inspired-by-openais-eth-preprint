import V8CapacityCRTFibers
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! V8 CRT instantiated in its literal integral source jet and its finite
receiver. The input descriptors are exactly independent constant and
higher Taylor digits over the original base ring. -/
namespace V8CapacityCRTJet
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityCRT

noncomputable section

variable (O : Type*) [CommRing O]

abbrev Jet (k : ℕ) := AdjoinRoot ((X:O[X])^k)

abbrev BaseMod (π : O) (P : ℕ) :=
  O ⧸ Ideal.span ({π^P}:Set O)

def constJet (k : ℕ) : O →+* Jet O k := AdjoinRoot.of ((X:O[X])^k)

def zJet (k : ℕ) : Jet O k := AdjoinRoot.root ((X:O[X])^k)

theorem zJet_nil (k : ℕ) : (zJet O k)^k=0 := by
  simpa only [eval₂_pow,eval₂_X,zJet] using AdjoinRoot.eval₂_root ((X:O[X])^k)

abbrev FiniteJet (π : O) (P k : ℕ) := Jet (BaseMod O π P) k

def coeffMod (π : O) (P : ℕ) : O →+* BaseMod O π P := Ideal.Quotient.mk _

def integralCoeff (π : O) (P k : ℕ) : O →+* FiniteJet O π P k :=
  (constJet (BaseMod O π P) k).comp (coeffMod O π P)

theorem p_nil (π : O) (P k : ℕ) : (integralCoeff O π P k π)^P=0 := by
  rw [← map_pow,integralCoeff,RingHom.comp_apply]
  have h : coeffMod O π P (π^P)=0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
  rw [h,map_zero]

/-- Input coefficients of the global decoder are in the actual integral
truncated jet ring, not artificially restricted to scalar constants. -/
def reduceJet (π : O) (P k : ℕ) : Jet O k →+* FiniteJet O π P k :=
  AdjoinRoot.lift (integralCoeff O π P k) (zJet (BaseMod O π P) k) (by
    rw [eval₂_pow,eval₂_X,zJet_nil])

theorem reduceJet_const (π : O) (P k : ℕ) (x : O) :
    reduceJet O π P k (constJet O k x)=integralCoeff O π P k x := by
  rw [reduceJet,constJet,AdjoinRoot.lift_of]

variable [IsLocalRing O]

theorem residue_diff_unit
    (d : IsLocalRing.ResidueField O → O)
    (hd : Function.RightInverse d (IsLocalRing.residue O))
    {a b : IsLocalRing.ResidueField O} (h : a≠b) : IsUnit (d a-d b) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [map_sub,hd,hd]
  exact sub_ne_zero.mpr h

def representative (a : IsLocalRing.ResidueField O) : O :=
  Classical.choose (IsLocalRing.residue_surjective a)

theorem representative_rightInverse :
    Function.RightInverse (representative O) (IsLocalRing.residue O) :=
  fun a => Classical.choose_spec (IsLocalRing.residue_surjective a)

variable {H : Type*} [Fintype H]
variable [Fintype (IsLocalRing.ResidueField O)]

local notation "R" => IsLocalRing.ResidueField O

/-- One finite chart with independent digit variables in the base domain.
The placement of the zero digit and each higher degree is faithful. -/
def digitInput (π : O) (P k : ℕ) (d : R → O)
    (a : H → R) (c : H → ℕ → O) : H → FiniteJet O π P k :=
  fun e => integralCoeff O π P k (d (a e)) +
    (integralCoeff O π P k π * integralCoeff O π P k (c e 0) +
    zJet (BaseMod O π P) k * ∑ j ∈ Finset.range (k-1),
      integralCoeff O π P k (c e (j+1)) * (zJet (BaseMod O π P) k)^j)

/-- The actual v8 raw independent-fiber conclusion. Choosing any fixed
coefficient readout, including the top truncated coefficient, commutes
with this construction. This claim does not include the Smith dimension. -/
theorem native_raw_columns {D : Type*} (π : O) (P k : ℕ)
    (d : R → O) (hd : Function.RightInverse d (IsLocalRing.residue O))
    (calcOutput : FiniteJet O π P k → D) (goal : (H → R) → (H → ℕ → O) → D) :
    (∃ C : MvPolynomial H (Jet O k), ∀ a c,
      calcOutput (MvPolynomial.eval₂Hom (reduceJet O π P k) (digitInput O π P k d a c) C)=goal a c) ↔
    (∀ a, ∃ C : MvPolynomial H (Jet O k), ∀ c,
      calcOutput (MvPolynomial.eval₂Hom (reduceJet O π P k) (digitInput O π P k d a c) C)=goal a c) := by
  let d' : R → Jet O k := fun x => constJet O k (d x)
  have hsep : ∀ a b, a≠b → IsUnit (d' a-d' b) := by
    intro a b hab
    change IsUnit (constJet O k (d a)-constJet O k (d b))
    rw [← map_sub]
    exact (residue_diff_unit O d hd hab).map (constJet O k)
  have hx (a : H → R) (v : H → ℕ → O) (e : H) :
      (digitInput O π P k d a v e - (reduceJet O π P k) (d' (a e)))^(P+k-1)=0 := by
    unfold digitInput d'
    rw [reduceJet_const,add_sub_cancel_left]
    exact two_ideal_power _ _ _ _ P k (p_nil O π P k) (zJet_nil (BaseMod O π P) k)
  exact raw_fiber_product (reduceJet O π P k) d' hsep (P+k-1)
    (digitInput O π P k d) calcOutput goal hx

#print axioms zJet_nil
#print axioms p_nil
#print axioms reduceJet_const
#print axioms residue_diff_unit
#print axioms representative_rightInverse
#print axioms native_raw_columns
end
end V8CapacityCRTJet
