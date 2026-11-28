import J6R49CostCoordinateBounds
import J6R49CostPositive
import J6R27PrescribedProbeBudget
import J6R19RetainedScalar

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13500000
set_option maxRecDepth 2400

/-! Quadratically reloaded actual positive probe words are not free:
the Lagrange phase on the genuine printed bank charges every read
and every encoding, as well as the independent sample providers. -/
namespace J6R49Cost
open scoped Polynomial
open AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J6R27PrescribedProbe J6R26StablePreparedRoot J6Mesh J6R14ZeroMode J6R28GeneratedRootFrame

theorem dimensions_to_probe_tariff {n e p ell B : ℕ}
    (hn : n ≤ B) (he : e ≤ B) (hp : p ≤ B) (hv : ell ≤ B) :
    n^2*(n*(e+2)+e*(p+6)+uvWidth e ell p+4) ≤ 16*(B+1)^5 := by
  calc
    _ ≤ B^2*(B*(B+2)+B*(B+6)+uvWidth B B B+4) := by unfold uvWidth; gcongr
    _ ≤ _ := by
      unfold uvWidth
      have E : 16*(B+1)^5=
          B^2*(B*(B+2)+B*(B+6)+(B*(B*B+1)+4)+4)+
          (15*B^5+78*B^4+151*B^3+152*B^2+80*B+16) := by ring
      rw [E]
      exact Nat.le_add_right _ _

theorem printed_probe_count_into_scale {m native s : ℕ} (hn : native ≤ m) (hm : M m ≤ s) :
    literalDegree m native+1 ≤ printedCoordinateScale s := by
  refine (printed_positive_probe_count_quadratic m native hn).trans ((show 2*(M m)^2+1 ≤ 2*s^2+1 by gcongr).trans ?_)
  unfold printedCoordinateScale
  have h : 64*(s+1)^4=(2*s^2+1)+(64*s^4+256*s^3+382*s^2+256*s+63) := by ring
  rw [h]
  exact Nat.le_add_right _ _

theorem literal_generated_probe_interp_budget
    {m native base ell : ℕ} (hn : native ≤ m) (f : ℤ[X]) (hf : f.Monic)
    (hfield : f.natDegree=printedFieldWidth m native)
    (hp : 0<J6SourcePrecision.printed m base) (hv : 0<ell)
    {fw : List (Word (J6SourcePrecision.printed m base))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (J6SourcePrecision.printed m base) f)
    (sample : Fin (literalDegree m native+1) → Meter (UVBlock fw ell)) :
    let d := literalDegree m native
    let s := enlargedScale m native base ell
    let fit := printed_nonzero_capacity m native f.natDegree hn hfield
    let hN := (J6R19Retained.size_of_monic_words hp hf hPoly).symm
    let A := generatedProbeBits f d fw.length hN fit
    let node := readPrescribed hp hv A.result.read
    interpBill node sample ≤ bill sample (probeOrder (d+1))+16*(printedCoordinateScale s+1)^5 := by
  let d := literalDegree m native
  let s := enlargedScale m native base ell
  let hN := (J6R19Retained.size_of_monic_words hp hf hPoly).symm
  let fit := printed_nonzero_capacity m native f.natDegree hn hfield
  have hc := generated_probe_interp_bill f hp hv hN fit sample
  have hm : M m ≤ s := (source_wires_le_twice_input m native hn).trans (by unfold s enlargedScale; omega)
  have hb : base ≤ s := by unfold s enlargedScale; omega
  have hV : ell ≤ s := by unfold s enlargedScale; omega
  have hE : f.natDegree ≤ printedCoordinateScale s :=
    hfield.le.trans (printed_degree_in_coordinate_scale hn hm)
  have h := dimensions_to_probe_tariff (printed_probe_count_into_scale hn hm) hE
    (printed_precision_in_coordinate_scale hm hb) (hV.trans printed_width_in_coordinate_scale)
  exact hc.trans (Nat.add_le_add_left h _)

#print axioms dimensions_to_probe_tariff
#print axioms printed_probe_count_into_scale
#print axioms literal_generated_probe_interp_budget
end J6R49Cost

