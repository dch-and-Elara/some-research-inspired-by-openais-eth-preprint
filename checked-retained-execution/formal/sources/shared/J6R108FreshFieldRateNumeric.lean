import J6R52FreshShapePaidSetup
import J6R49CostDimensions

/-! Original exhaustive binary field search followed by exact literal
coefficient-word widening. Both stages of the actual R52 paid frame
are charged here, using the true guarded source dimensions. -/
namespace J6R108FreshFieldRate
open scoped Polynomial Classical
open Polynomial Std.Sat J6Mesh J7R10Plant AOracleMachineTime
open J6R28GeneratedRootFrame J6R24LegalLayout J6R24MeteredRecursion J6R29BinaryFieldSearch
open J6R26StablePreparedRoot J6R51Ingress J6R12Blueprint J6R11Repack J6R12Repack J6ActiveRun
open J6R52FreshShape J6R27PrescribedProbe J6R49Cost A1R10

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 14000000
set_option maxRecDepth 3200

def searchConstant : ℕ := 1024*9^2*2*2^6
def freshFieldSourceRoof (s base : ℕ) : ℕ :=
  searchConstant*s^8 + 20 + 8*s*(4*(base+160*s^2)+6)

theorem physical_source_has_positive_field_degree (m n : ℕ) (hn : n≤m) :
    1<physicalSize m n := by
  by_contra h
  have z := Nat.clog_of_right_le_one (Nat.le_of_not_gt h) 2
  have p := printed_field_width_positive m n hn
  unfold printedFieldWidth at p
  rw [z,Nat.mul_zero] at p
  omega

theorem literal_degree_and_precision_component_bounds (m n base : ℕ) (hn : n≤m) :
    printedFieldWidth m n≤8*physicalSize m n ∧
      J6SourcePrecision.printed m base≤base+160*(physicalSize m n)^2 := by
  let s := physicalSize m n
  have wires : M m≤2*s := source_wires_le_twice_input m n hn
  constructor
  · calc
      _ ≤ 4*M m := printed_field_linear m n hn
      _ ≤ 4*(2*s) := Nat.mul_le_mul_left _ wires
      _ = _ := by ring
  · calc
      _ ≤ base+40*(M m)^2 := printed_precision_quadratic m base
      _ ≤ base+40*(2*s)^2 := Nat.add_le_add_left
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left wires 2)) _
      _ = _ := by ring

theorem full_fresh_roof_polynomial_on_original_base_domain (s base C : ℕ)
    (hs : 0<s) (fit : base≤C*s) :
    freshFieldSourceRoof s base≤(searchConstant+32*C+5188)*s^8 := by
  have squared : s≤s^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (show 1≤2 by decide)
  have hB : base+160*s^2≤(C+160)*s^2 := by
    rw [Nat.add_mul]
    exact Nat.add_le_add_right (fit.trans (Nat.mul_le_mul_left C squared)) _
  have h1 : s≤s^8 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (show 1≤8 by decide)
  have h3 : s^3≤s^8 := Nat.pow_le_pow_right hs (by decide)
  have h0 : 1≤s^8 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right hs (show 0≤8 by decide)
  calc
    _ ≤ searchConstant*s^8+20 + 8*s*(4*((C+160)*s^2)+6) := by
      unfold freshFieldSourceRoof
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _
        (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hB) 6)) _
    _ = searchConstant*s^8+ (32*(C+160)*s^3+48*s+20*1) := by ring
    _ ≤ searchConstant*s^8+ (32*(C+160)*s^8+48*s^8+20*s^8) :=
      Nat.add_le_add_left (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h3)
        (Nat.mul_le_mul_left _ h1)) (Nat.mul_le_mul_left _ h0)) _
    _ = _ := by ring

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (F : CNF V) (order : DeclaredOrder V)
local notation "H" => (guardedInOrder F order.roster)
local notation "m" => (nWires H)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)
local notation "S" => (physicalSize m n)

theorem real_paid_fresh_field_frame_source_roof (base : ℕ) :
    (paidFreshFieldFrame F order base).steps≤freshFieldSourceRoof S base := by
  have hn : n≤m := fresh_source_native_fits F order
  have dim := literal_degree_and_precision_component_bounds m n base hn
  have search : (freshFieldSearch F order).steps≤searchConstant*S^8+6 :=
    generated_native_field_poly m n hn
  have exactFrame := (fresh_searched_frame_receipt F order base).2.2.2.2
  have frame : (freshFieldFrame F order base).steps ≤
      4+8*S*(4*(base+160*S^2)+6)+3 := by
    rw [exactFrame]
    unfold frameBuildFee
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul dim.1
      (Nat.add_le_add_right (Nat.mul_le_mul_left 4 dim.2) 6)) 4) 3
  rw [(paid_fresh_field_frame_actual F order base).2.1]
  have sum := Nat.add_le_add_right (Nat.add_le_add search frame) 7
  unfold freshFieldSourceRoof
  omega

theorem actual_root_field_is_generated_and_polynomial (base C : ℕ) (fit : base≤C*S) :
    let A := paidFreshFieldFrame F order base
    let R := freshFieldSearch F order
    let f := (freshFieldResult F order).f
    f.Monic ∧ Irreducible (NativeProbeRing.residuePoly f) ∧
      (fieldSearch (printedFieldWidth m n)).result=some R.result.lower ∧
      A.result.words=R.result.lower.val.map (zeroExtend (J6SourcePrecision.printed m base)) ∧
      A.steps≤(searchConstant+32*C+5188)*S^8 := by
  obtain ⟨monic,irred⟩ := generated_fresh_field_is_permitted F order
  have body := fresh_searched_frame_receipt F order base
  have same := (paid_fresh_field_frame_actual F order base).1
  have lit : (paidFreshFieldFrame F order base).result.words=
      (freshFieldSearch F order).result.lower.val.map (zeroExtend (J6SourcePrecision.printed m base)) :=
    (congrArg (fun Q=>Q.words) same).trans body.2.2.1
  have hs : 0<S := Nat.zero_lt_one.trans
    (physical_source_has_positive_field_degree m n (fresh_source_native_fits F order))
  exact ⟨monic,irred,body.1,lit,(real_paid_fresh_field_frame_source_roof F order base).trans
    (full_fresh_roof_polynomial_on_original_base_domain S base C hs fit)⟩

#print axioms physical_source_has_positive_field_degree
#print axioms literal_degree_and_precision_component_bounds
#print axioms full_fresh_roof_polynomial_on_original_base_domain
#print axioms real_paid_fresh_field_frame_source_roof
#print axioms actual_root_field_is_generated_and_polynomial
end
end J6R108FreshFieldRate
