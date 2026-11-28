import V8CapacityDigitChart
import V8CapacityCRTJet

/-! Select literal base-q digit nodes for every finite residue field.
The chosen chart used by S2 imposes no additional restriction on a DVR. -/
namespace V8CapacityUnified.Scalar
open scoped Classical
open V8CapacityDigits V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false

variable (O : Type*) [CommRing O] [IsLocalRing O] [Fintype (IsLocalRing.ResidueField O)]
local notation "κ" => IsLocalRing.ResidueField O
local notation "q" => Fintype.card κ

theorem residue_card_two : 2≤q :=
  Fintype.one_lt_card

theorem residue_card_pos : 0<q := by have h := residue_card_two O; omega

def zeroSection (a : κ) : O := if a=0 then 0 else representative O a

theorem zeroSection_inverse : Function.RightInverse (zeroSection O) (IsLocalRing.residue O) := by
  intro a
  by_cases h : a=0
  · subst a
    simp [zeroSection]
  · rw [zeroSection,if_neg h]
    exact representative_rightInverse O a

def enumeration : Fin q ≃ κ :=
  let e := (Fintype.equivFin κ).symm
  e.trans (Equiv.swap (e ⟨0,residue_card_pos O⟩) 0)

theorem enumeration_zero : enumeration O ⟨0,residue_card_pos O⟩=0 := by
  simp [enumeration]

variable {π : O} (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))

def exactDVRDigits : Digits π q :=
  fromLocalResidue π hMax (enumeration O) (zeroSection O) (zeroSection_inverse O)

theorem exactDVRDigits_zero : (exactDVRDigits O hMax).d ⟨0,residue_card_pos O⟩=0 := by
  change zeroSection O (enumeration O ⟨0,residue_card_pos O⟩)=0
  exact (congrArg (zeroSection O) (enumeration_zero O)).trans (by simp [zeroSection])

#print axioms residue_card_two
#print axioms zeroSection_inverse
#print axioms enumeration_zero
#print axioms exactDVRDigits_zero
end
end V8CapacityUnified.Scalar
