import J6R27PrescribedProbeCapacity
import J6R28GeneratedRootFrameWidth
import J6R28GeneratedRootFrameLiteral
import J6R24MeteredRecursionTight

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

/-! Printed J6 dimensions, with bounds in the enlarged physical size
rather than arbitrary supplied register depths or estimator parameters. -/
namespace J6R49Cost
open J6Mesh J6SourcePrecision J6R14ZeroMode J6R22RootReadout
open J6R27PrescribedProbe J6R28GeneratedRootFrame

def enlargedScale (m native base ell : ℕ) := 2*physicalSize m native+base+ell+1

theorem m_plus_two_le_physical_wires (m : ℕ) : m+2≤M m := by
  have h : b m≤lambda m := by unfold lambda; omega
  exact (dyadic_rounding m).1.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) h)

theorem source_wires_le_twice_input (m native : ℕ) (hn : native≤m) :
    M m≤2*physicalSize m native := by
  have h : 0<lambda m := by have := b_pos m; unfold lambda; omega
  have hEq : M m=2*2^(lambda m-1) := by
    unfold M
    have hn : lambda m = (lambda m-1)+1 := by omega
    calc
      _ = 2^((lambda m-1)+1) := congrArg (fun n:ℕ=>(2:ℕ)^n) hn
      _ = _ := by rw [pow_succ,Nat.mul_comm]
  rw [hEq]
  exact Nat.mul_le_mul_left _ ((physicalSize_ceiling m native hn).1).le

theorem printed_dimension_le_wires (m : ℕ) : a m+1≤M m :=
  (J9PrintedSchedule.next_le_two_power (a m)).trans (mesh_length_le_edges m)

theorem printed_precision_quadratic (m base : ℕ) :
    J6SourcePrecision.printed m base≤base+40*(M m)^2 := by
  have hk : u m+1≤M m := by
    have he : u m+1≤a m+1 := by unfold u a; omega
    exact he.trans (printed_dimension_le_wires m)
  have hu : 0<u m := by have := b_pos m; unfold u; omega
  have hc : J6SourcePrecision.h m≤4*M m :=
    J6R24MeteredRecursion.simple_height_cap hu (Nat.le_of_succ_le hk)
  calc
    _ ≤ base+8*(4*M m)*(M m)+8*M m*M m := by
      unfold J6SourcePrecision.printed
      gcongr
      · exact mesh_length_le_edges m
      · exact printed_dimension_le_wires m
    _ = _ := by ring

theorem printed_field_linear (m native : ℕ) (hn : native≤m) :
    printedFieldWidth m native≤4*M m := by
  unfold printedFieldWidth
  rw [(physicalSize_ceiling m native hn).2.2]
  exact Nat.mul_le_mul_left _ (Nat.le_of_succ_le (J9PrintedSchedule.next_le_two_power (lambda m)))

theorem printed_positive_probe_count_quadratic (m native : ℕ) (hn : native≤m) :
    literalDegree m native+1≤2*(M m)^2+1 := by
  rw [literal_degree_eq m native hn]
  have h := (Nat.sub_le (2*L m) 1).trans (Nat.mul_le_mul_left 2 (mesh_length_le_edges m))
  calc
    _≤M m*(2*M m)+1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _
    _=_ := by ring

theorem printed_factor_width_quartic {m q s : ℕ} (hm : M m≤s) (hq : q≤s) :
    printedFactorWidth m q≤16*(s+1)^4 := by
  have hm0 : m≤s := (Nat.le_add_right m 2).trans ((m_plus_two_le_physical_wires m).trans hm)
  have ha := (printed_dimension_le_wires m).trans hm
  have hPad : literalPadCount m≤s := by
    have h := literal_pad_count_source m
    have hM : literalPadCount m≤M m := by omega
    exact hM.trans hm
  calc
    _≤((2*s+1)*s)^2+s*(2*s+1)+(2*((2*s+1)*s)+3)*s+2 := by
      unfold printedFactorWidth publicFactorWidth outerMeshWidth
      rw [pow_two]
      gcongr
    _≤16*(s+1)^4 := by
      have E : 16*(s+1)^4=
        (((2*s+1)*s)^2+s*(2*s+1)+(2*((2*s+1)*s)+3)*s+2)+
          (12*s^4+56*s^3+91*s^2+60*s+14) := by ring
      rw [E]
      exact Nat.le_add_right _ _

#print axioms source_wires_le_twice_input
#print axioms printed_dimension_le_wires
#print axioms printed_precision_quadratic
#print axioms printed_field_linear
#print axioms printed_positive_probe_count_quadratic
#print axioms printed_factor_width_quartic
end J6R49Cost

