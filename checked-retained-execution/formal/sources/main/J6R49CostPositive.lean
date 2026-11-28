import J6R49CostDimensions
import J6R27PrescribedProbeRead

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6400000

/-! Build and scan the actual positive bits, at the real J6 outer
probe count M(2L-1)+1. Nobody supplies a free binary probe mask.
Generation is charged once; each scan has its own stated charge. -/
namespace J6R49Cost
open scoped Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6R14ZeroMode J6R27PrescribedProbe J6R28GeneratedRootFrame

theorem positive_builder_polynomial {e n s : ℕ} (he : e≤4*s) (hn : n≤2*s^2+1) :
    positiveTapeFee e n+3≤200*(s+1)^3 := by
  calc
    _≤positiveTapeFee (4*s) (2*s^2+1)+3 := by unfold positiveTapeFee; gcongr
    _≤_ := by
      have h : 200*(s+1)^3=
          (positiveTapeFee (4*s) (2*s^2+1)+3)+(40*s^3+588*s^2+508*s+181) := by
        unfold positiveTapeFee
        ring
      rw [h]
      exact Nat.le_add_right _ _

theorem positive_read_polynomial {e n s : ℕ} (he : e≤4*s) (hn : n≤2*s^2+1) :
    n*(e+2)≤16*(s+1)^3 := by
  calc
    _≤(2*s^2+1)*(4*s+2) := Nat.mul_le_mul hn (Nat.add_le_add_right he _)
    _≤_ := by
      have h : 16*(s+1)^3=(2*s^2+1)*(4*s+2)+(8*s^3+44*s^2+44*s+14) := by ring
      rw [h]
      exact Nat.le_add_right _ _

theorem true_printed_positive_bank
    (f : ℤ[X]) (m native base ell : ℕ) (hn : native≤m)
    (hfield : f.natDegree=printedFieldWidth m native) :
    let d := literalDegree m native
    let B := generatedProbeBits f d f.natDegree rfl (printed_nonzero_capacity m native f.natDegree hn hfield)
    let s := enlargedScale m native base ell
    B.steps=positiveTapeFee f.natDegree (d+1)+3 ∧
      B.steps≤200*(s+1)^3 ∧
      ∀ i : Fin (d+1), (B.result.read i).result.val=encodeBits f.natDegree (i.val+1) ∧
        (B.result.read i).steps≤16*(s+1)^3 := by
  let d := literalDegree m native
  let s := enlargedScale m native base ell
  let fit : d+1<2^f.natDegree := printed_nonzero_capacity m native f.natDegree hn hfield
  have hh : M m≤s := (source_wires_le_twice_input m native hn).trans (by unfold s enlargedScale; omega)
  have he : f.natDegree≤4*s :=
    hfield.le.trans ((printed_field_linear m native hn).trans (Nat.mul_le_mul_left 4 hh))
  have hD : d+1≤2*s^2+1 := by
    have h := printed_positive_probe_count_quadratic m native hn
    exact h.trans (by gcongr)
  obtain ⟨hBuild,hRead⟩ := generated_probe_bits_receipt f d f.natDegree rfl fit
  refine ⟨hBuild,hBuild.le.trans (positive_builder_polynomial he hD),?_⟩
  intro i
  exact ⟨(hRead i).1,(hRead i).2.trans (positive_read_polynomial he hD)⟩

#print axioms positive_builder_polynomial
#print axioms positive_read_polynomial
#print axioms true_printed_positive_bank
end J6R49Cost

