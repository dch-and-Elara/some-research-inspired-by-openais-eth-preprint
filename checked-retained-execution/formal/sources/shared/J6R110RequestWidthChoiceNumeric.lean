import J6R54PublicFamilySite
import J6R49CostDimensions

/-! Concrete widths for the original public odd-centre requests and
their true exterior edge-count lane. These are chosen before encoding,
not inferred from arbitrary already published words. -/
namespace J6R110RequestWidthChoice
open J6Mesh J6R27PrescribedProbe J6R49Cost J6R54PublicFamily J6R14ZeroMode

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 6250000

def centreWidth (m : ℕ) : ℕ := lambda m+1
def sampleWidth (m : ℕ) : ℕ := 2*lambda m+2
def magnitudeWidth (m : ℕ) : ℕ := centreWidth m
def edgeWidth (m : ℕ) : ℕ := lambda m+2

theorem chosen_centre_includes_last_odd (m : ℕ) :
    2*m+1<2^centreWidth m := by
  have h := m_plus_two_le_physical_wires m
  rw [centreWidth,pow_succ,←show M m=2^lambda m from rfl]
  omega

theorem chosen_sample_includes_degree_endpoint (m native : ℕ) (nativeFit : native≤m) :
    literalDegree m native<2^sampleWidth m := by
  have d := printed_positive_probe_count_quadratic m native nativeFit
  have cap : literalDegree m native≤2*(M m)^2 := by omega
  have pow : (2:ℕ)^sampleWidth m=4*(M m)^2 := by
    unfold sampleWidth M
    rw [pow_add,mul_comm 2 (lambda m),pow_mul]
    norm_num
    ring
  rw [pow]
  exact cap.trans_lt (Nat.mul_lt_mul_of_pos_right (by decide) (by unfold M; positivity))

theorem chosen_edge_includes_double_physical_size (m native : ℕ) (nativeFit : native≤m) :
    2*physicalSize m native<2^edgeWidth m := by
  have small := (physicalSize_ceiling m native nativeFit).2.1
  have pow : (2:ℕ)^edgeWidth m=4*M m := by
    unfold edgeWidth M
    rw [pow_add]
    norm_num
    ring
  rw [pow]
  have pos : 0<M m := by unfold M; positivity
  omega

def chooseWidths (m native : ℕ) (nativeFit : native≤m) :
    Widths m native (centreWidth m) (sampleWidth m) (magnitudeWidth m) (edgeWidth m) where
  centrePos := by unfold centreWidth; omega
  samplePos := by unfold sampleWidth; omega
  centreFit := chosen_centre_includes_last_odd m
  sampleFit := chosen_sample_includes_degree_endpoint m native nativeFit
  magnitudeFit := chosen_centre_includes_last_odd m
  edgePos := by unfold edgeWidth; omega
  edgeFit := chosen_edge_includes_double_physical_size m native nativeFit

theorem chosen_request_widths_are_logarithmic_in_the_actual_source
    (m native : ℕ) (nativeFit : native≤m) :
    let s := physicalSize m native
    centreWidth m=Nat.clog 2 s+1 ∧ sampleWidth m=2*Nat.clog 2 s+2 ∧
      magnitudeWidth m=Nat.clog 2 s+1 ∧ edgeWidth m=Nat.clog 2 s+2 := by
  dsimp only
  rw [(physicalSize_ceiling m native nativeFit).2.2]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem chosen_request_widths_polynomial_bounds
    (m native : ℕ) (nativeFit : native≤m) :
    let s := physicalSize m native
    centreWidth m≤2*s+1 ∧ sampleWidth m≤4*s+2 ∧
      magnitudeWidth m≤2*s+1 ∧ edgeWidth m≤2*s+2 := by
  let s := physicalSize m native
  have h : lambda m≤2*s := (Nat.lt_pow_self (n:=lambda m) (a:=2) (by decide)).le.trans
    (source_wires_le_twice_input m native nativeFit)
  change centreWidth m≤2*s+1 ∧ sampleWidth m≤4*s+2 ∧
    magnitudeWidth m≤2*s+1 ∧ edgeWidth m≤2*s+2
  unfold magnitudeWidth centreWidth sampleWidth edgeWidth
  omega

theorem true_request_dimensions_polynomial
    (m native : ℕ) (nativeFit : native≤m) :
    let s := physicalSize m native
    m+1≤2*s ∧ 2*m+1≤4*s ∧ literalDegree m native+1≤8*s^2+1 := by
  let s := physicalSize m native
  have sM : M m≤2*s := source_wires_le_twice_input m native nativeFit
  have mM : m+2≤M m := m_plus_two_le_physical_wires m
  have sample : literalDegree m native+1≤8*s^2+1 := by
    calc
      _≤2*(M m)^2+1 := printed_positive_probe_count_quadratic m native nativeFit
      _≤2*(2*s)^2+1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left sM 2)) _
      _=_ := by ring
  exact ⟨by omega,by omega,sample⟩

theorem chosen_marked_key_width (m kp : ℕ) :
    KeyWidth kp (centreWidth m) (sampleWidth m)=kp+3*lambda m+9 := by
  unfold KeyWidth centreWidth sampleWidth
  omega

#print axioms chosen_centre_includes_last_odd
#print axioms chosen_sample_includes_degree_endpoint
#print axioms chosen_edge_includes_double_physical_size
#print axioms chooseWidths
#print axioms chosen_request_widths_are_logarithmic_in_the_actual_source
#print axioms chosen_request_widths_polynomial_bounds
#print axioms true_request_dimensions_polynomial
#print axioms chosen_marked_key_width
end J6R110RequestWidthChoice

