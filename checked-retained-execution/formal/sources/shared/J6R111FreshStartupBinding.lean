import J6R110FreshImageRate
import J6R110RootWidthChoiceProducer
import J6R110RequestWidthChoiceNumeric

/-! One actual fresh startup: emit the chosen base word once, use its
result as the existing R54 FreshWords field, and invoke the original
R57 request-image builder with the selected legal address widths. -/
namespace J6R111FreshStartupBinding
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R51Ingress
open J6R49RootIngress J6R50RootIngress J6R52FreshShape J6R52FreshExterior J6R15ModeCost
open J6R27PrescribedProbe J6R54PublicFamily J6R57PublicRequest
open J6R110RequestImageRate J6R110FreshImageRate J6R109FreshLiteralBound J6R108FreshFieldRate
open J6R110RootWidthChoice J6R110RequestWidthChoice

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 3600
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 7

universe u v
private abbrev domain {D : Sort u} {A : D→Sort v} (_ : (x : D)→A x) : Sort u := D

noncomputable section
private def actualAtThree {V : Type} [a : DecidableEq V] [b : Fintype V] [Nonempty V]
    (F : CNF V) (order : DeclaredOrder V) (h d j r c e base ell q prec kp bw : ℕ)
    (three : ∀ row∈F,row.length≤3) :=
  @freshSharedInputs V a b inferInstance F order h d j r c e base ell q prec kp bw three

section Original
variable {V : Type} [a : DecidableEq V] [b : Fintype V] [Nonempty V]
variable (F : CNF V) (order : DeclaredOrder V)
local notation "Graph" => (guardedInOrder F order.roster)
local notation "m" => (nWires Graph)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)
local notation "s" => (physicalSize m n)
local notation "q0" => (chosenQ m)
local notation "p0" => (chosenPrec m)
local notation "w0" => (chosenBW m)

/-- Only the original source premises and the actual marker. Neither
FreshWords nor Widths is supplied. -/
structure RawStartup (h d j r c e base ell kp : ℕ) where
  three : ∀ row∈F,row.length≤3
  large : printedGuard m n
  positive : 0<ell
  guards : @SerialGuards V a b F order h d j r c e
  code : V→List Bool
  inj : Function.Injective code
  declared : List (List Bool)
  body : BitsCNF
  declaredExact : declared=order.roster.map code
  bodyExact : body=codeCNF code F
  mark : Word kp

variable {F order}
variable {h d j r c e base ell kp : ℕ}
variable (A : RawStartup F order h d j r c e base ell kp)

def originalInputsAtGeneratedWords (words : FreshWords m base q0 p0 kp w0) :=
  actualAtThree F order h d j r c e base ell q0 p0 kp w0 A.three A.large A.positive words
    A.guards A.code A.inj A.declared A.body A.declaredExact A.bodyExact

def initialPaidWords (fit : base≤s^2) :=
  makeFreshWords m n base (fresh_source_native_fits F order) fit A.mark

def selectedStartup (fit : base≤s^2) :=
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let K := initialPaidWords A fit
  let I := originalInputsAtGeneratedWords A K.result
  let W := chooseWidths m n (fresh_source_native_fits F order)
  let J := buildRequestImage W I
  (⟨J.result,K.steps+J.steps⟩ : Meter _)

theorem same_request_image_and_one_real_width_emission (fit : base≤s^2) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let K := initialPaidWords A fit
    let I := originalInputsAtGeneratedWords A K.result
    let W := chooseWidths m n (fresh_source_native_fits F order)
    let J := buildRequestImage W I
    let out := selectedStartup A fit
    out.result=J.result ∧ out.steps=ordinalFee q0 base+J.steps := by
  let H := fresh_source_native_fits F order
  have fee := (made_fresh_words_has_actual_base_and_numeric_code m n base H fit A.mark).2.2.2.2
  exact ⟨rfl,congrArg (fun x : ℕ=>x+_) fee⟩

theorem literal_chosen_startup_uses_original_closed_input_rate
    (w C : ℕ) (width : ∀ x,(A.code x).length=w)
    (fit : base≤C*s) (constant : C≤s) :
    let fit0 := source_base_domain_implies_square_bound fit constant
    let K := initialPaidWords A fit0
    let I := originalInputsAtGeneratedWords A K.result
    let out := selectedStartup A fit0
    let f := (freshFieldResult F order).f
    out.steps≤ordinalFee q0 base+
      (freshLiteralRoof h d j r c w 3 F.length order.roster.length m+
      (searchConstant+32*C+5188)*s^8+
      precisionFromBaseFee m q0+exteriorRegistersFee q0 q0 p0+ordinalFee w0 I.code+15+
      commonRootClock m n f.natDegree q0 (J6SourcePrecision.printed m base) r c d+
      catalogueClock m n kp (centreWidth m) (sampleWidth m) (magnitudeWidth m)+8) := by
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let fit0 := source_base_domain_implies_square_bound fit constant
  let K := initialPaidWords A fit0
  let W := chooseWidths m n (fresh_source_native_fits F order)
  have exactFee := (same_request_image_and_one_real_width_emission A fit0).2
  have old := original_request_image_has_closed_input_generation_cost F order base ell q0 p0 kp w0
    A.three A.large A.positive K.result A.guards A.code A.inj A.declared A.body
    A.declaredExact A.bodyExact w C width fit W
  exact exactFee.le.trans (Nat.add_le_add_left old (ordinalFee q0 base))

#print axioms originalInputsAtGeneratedWords
#print axioms initialPaidWords
#print axioms selectedStartup
#print axioms same_request_image_and_one_real_width_emission
#print axioms literal_chosen_startup_uses_original_closed_input_rate
end Original
end
end J6R111FreshStartupBinding
