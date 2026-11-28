import J6R110RequestImageRate
import J6R109SharedLiteralRate
import J6R108FreshFieldRateShared

namespace J6R110FreshImageRate
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R51Ingress
open J6R49RootIngress J6R50RootIngress J6R52FreshShape J6R52FreshExterior J6R15ModeCost
open J6R27PrescribedProbe J6R54PublicFamily J6R57PublicRequest
open J6R110RequestImageRate J6R109FreshLiteralBound J6R109SharedLiteralRate J6R108FreshFieldRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3200
set_option maxSynthPendingDepth 7

universe u v
private abbrev domain {D : Sort u} {T : D→Sort v} (_ : (x : D)→T x) : Sort u := D

noncomputable section
private def actualAtThree {V : Type} [D : DecidableEq V] [Fin : Fintype V] [Nonempty V]
    (F : CNF V) (order : DeclaredOrder V) (h d j r c e base ell q prec kp bw : ℕ)
    (three : ∀ row∈F,row.length≤3) :=
  @freshSharedInputs V D Fin inferInstance F order h d j r c e base ell q prec kp bw three

theorem original_request_image_has_closed_input_generation_cost
    {V : Type} [a : DecidableEq V] [b : Fintype V] [Nonempty V]
    (F : CNF V) (order : DeclaredOrder V) {h d j r c e : ℕ}
    (base ell q prec kp bw : ℕ) (three : ∀ row∈F,row.length≤3)
    (large : domain (actualAtThree F order h d j r c e base ell q prec kp bw three))
    (positive : 0<ell)
    (words : domain (actualAtThree F order h d j r c e base ell q prec kp bw three large positive))
    (guards : @SerialGuards V a b F order h d j r c e)
    (code : V→List Bool) (inj : Function.Injective code)
    (declared : List (List Bool)) (body : BitsCNF)
    (declaredExact : declared=order.roster.map code) (bodyExact : body=codeCNF code F)
    (w C : ℕ) (width : ∀ v, (code v).length=w)
    (fit : base≤C*physicalSize (nWires (guardedInOrder F order.roster))
      (Paper6SourceSize.sourceNativeSize F order))
    {tc tj tw edgew : ℕ}
    (W : Widths (nWires (guardedInOrder F order.roster)) (Paper6SourceSize.sourceNativeSize F order)
      tc tj tw edgew) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let m := nWires (guardedInOrder F order.roster)
    let n := Paper6SourceSize.sourceNativeSize F order
    let s := physicalSize m n
    let f := (freshFieldResult F order).f
    let I := actualAtThree F order h d j r c e base ell q prec kp bw three large positive words
      guards code inj declared body declaredExact bodyExact
    (buildRequestImage W I).steps≤freshLiteralRoof h d j r c w 3 F.length order.roster.length m+
      (searchConstant+32*C+5188)*s^8+
      precisionFromBaseFee m q+exteriorRegistersFee q q prec+ordinalFee bw I.code+15+
      commonRootClock m n f.natDegree q (J6SourcePrecision.printed m base) r c d+
      catalogueClock m n kp tc tj tw+8 := by
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let I := actualAtThree F order h d j r c e base ell q prec kp bw three large positive words
    guards code inj declared body declaredExact bodyExact
  have lit := fresh_shared_literal_is_actual_and_source_polynomial F order base ell q prec kp bw
    three large positive words guards code inj declared body declaredExact bodyExact w width
  have field := fresh_shared_field_is_actual_and_source_polynomial F order base ell q prec kp bw
    three large positive words guards code inj declared body declaredExact bodyExact C fit
  refine (compiled_request_image_price_from_two_actual_input_producers W I).trans ?_
  dsimp only at lit field ⊢
  gcongr
  · exact lit
  · exact field

#print axioms original_request_image_has_closed_input_generation_cost
end
end J6R110FreshImageRate
