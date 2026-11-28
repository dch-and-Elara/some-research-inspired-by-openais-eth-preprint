import J6R49CostDimensions
import J6R49CostSampleBounds
import J6R22RootReadoutTop

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

/-! Explicit printed-scale polynomials for the actual root coordinate decoder.
No cost for creating an arbitrary received U/V slot is inferred. -/
namespace J6R49Cost
open AOracleMachineTime J6Mesh J6R14ZeroMode J6R22RootReadout J6R28GeneratedRootFrame

def printedCoordinateScale (s : ℕ) := 64*(s+1)^4

theorem printed_answer_width_quartic {m base s : ℕ} (hm : M m≤s) (hb : base≤s) :
    printedAnswerWidth m base≤printedCoordinateScale s := by
  have hm0 : m≤s := (Nat.le_add_right m 2).trans ((m_plus_two_le_physical_wires m).trans hm)
  have ha := (printed_dimension_le_wires m).trans hm
  have hp : J6SourcePrecision.printed m base≤s+40*s^2 := by
    exact (printed_precision_quadratic m base).trans (by gcongr)
  let b := (2*s+1)*s
  calc
    _≤(s+40*s^2+b*s+(2*b+1)*s+1)*(s+1)+3 := by
      unfold printedAnswerWidth baseTermWidth outerMeshWidth b
      gcongr
    _≤printedCoordinateScale s := by
      unfold printedCoordinateScale b
      have h : 64*(s+1)^4=
          (s+40*s^2+((2*s+1)*s)*s+(2*((2*s+1)*s)+1)*s+1)*(s+1)+3+
            (58*s^4+207*s^3+339*s^2+253*s+60) := by ring
      rw [h]
      exact Nat.le_add_right _ _

theorem printed_precision_in_coordinate_scale {m base s : ℕ} (hm : M m≤s) (hb : base≤s) :
    J6SourcePrecision.printed m base≤printedCoordinateScale s := by
  refine (printed_precision_quadratic m base).trans ((show base+40*(M m)^2≤s+40*s^2 by gcongr).trans ?_)
  unfold printedCoordinateScale
  have h : 64*(s+1)^4=s+40*s^2+(64*s^4+256*s^3+344*s^2+255*s+64) := by ring
  rw [h]
  exact Nat.le_add_right _ _

theorem printed_width_in_coordinate_scale {s : ℕ} : s≤printedCoordinateScale s := by
  unfold printedCoordinateScale
  have h : 64*(s+1)^4=s+(64*s^4+256*s^3+384*s^2+255*s+64) := by ring
  rw [h]
  exact Nat.le_add_right _ _

theorem printed_degree_in_coordinate_scale {m native s : ℕ}
    (hn : native≤m) (hm : M m≤s) : printedFieldWidth m native≤printedCoordinateScale s := by
  refine (printed_field_linear m native hn).trans ((Nat.mul_le_mul_left 4 hm).trans ?_)
  unfold printedCoordinateScale
  have h : 64*(s+1)^4=4*s+(64*s^4+256*s^3+384*s^2+252*s+64) := by ring
  rw [h]
  exact Nat.le_add_right _ _

theorem mesh_word_tariff_poly {p m T : ℕ} (hp : p≤T) (hm : m≤T) :
    28*p+24+(2*m+1)*meshStateFee p≤400*(T+1)^3 := by
  calc
    _ ≤ 28*T+24+(2*T+1)*meshStateFee T := by unfold meshStateFee; gcongr
    _ ≤ _ := by
      unfold meshStateFee
      have h : 400*(T+1)^3=
          28*T+24+(2*T+1)*(5*(32*(T+1)^2)+16*T+18)+
            (80*T^3+368*T^2+480*T+198) := by ring
      rw [h]
      exact Nat.le_add_right _ _

theorem coordinate_machine_tariff_poly {P B R ell degree m e T : ℕ}
    (hP : P≤T) (hB : B≤T) (hR : R≤T) (hℓ : ell≤T)
    (hd : degree≤T) (hm : M m≤T) (he : e≤T) :
    makeCoordinateFee P B R ell degree m e≤2000*(T+1)^6 := by
  have h0 := (Nat.le_add_right m 2).trans ((m_plus_two_le_physical_wires m).trans hm)
  have h1 := mesh_word_tariff_poly hP h0
  have h2 := mesh_word_tariff_poly hR h0
  have h3 := sample_word_tariff_poly hd hℓ hP hB hm he
  have h4 : (T+1)^3≤(T+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have h5 : 19*R+6+10≤50*(T+1)^3 := by
    calc
      _≤19*T+6+10 := by omega
      _≤_ := by
        have h : 50*(T+1)^3=(19*T+6+10)+(50*T^3+150*T^2+131*T+34) := by ring
        rw [h]
        exact Nat.le_add_right _ _
  change (28*P+24+(2*m+1)*meshStateFee P)+sampleWordTariff degree ell P B (M m) e+
    (28*R+24+(2*m+1)*meshStateFee R)+(19*R+6)+10≤_
  omega

#print axioms printed_answer_width_quartic
#print axioms printed_precision_in_coordinate_scale
#print axioms printed_width_in_coordinate_scale
#print axioms printed_degree_in_coordinate_scale
#print axioms mesh_word_tariff_poly
#print axioms coordinate_machine_tariff_poly
end J6R49Cost

