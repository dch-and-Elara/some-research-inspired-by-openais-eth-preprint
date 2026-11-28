import J6R108FreshFieldRateNumeric
import J6R54PublicFamilyFresh

/-! Read the charged field from the very fresh shared inputs consumed
by the selected outer request image. The true frame is retained and
the search/padding bill occurs once, not once per query/group. -/
namespace J6R108FreshFieldRate
open scoped Polynomial Classical
open Polynomial Std.Sat AOracleMachineTime
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R51Ingress
open J6R49RootIngress J6R50RootIngress J6R52FreshShape J6R52FreshExterior J6R15ModeCost
open J6R27PrescribedProbe J6R54PublicFamily

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 1400
set_option maxSynthPendingDepth 7

universe u v
private abbrev binderDomain {D : Sort u} {T : D→Sort v} (_ : (a : D)→T a) : Sort u := D

noncomputable section
private def headAtThree {V : Type} [a : DecidableEq V] [b : Fintype V] [Nonempty V]
    (F : CNF V) (order : DeclaredOrder V) (h d j r c e base ell q prec kp bw : ℕ)
    (three : ∀ row∈F,row.length≤3) :=
  @J6R54PublicFamily.freshSharedInputs V a b inferInstance F order h d j r c e base ell q prec kp bw three

theorem fresh_shared_field_is_actual_and_source_polynomial
    {V : Type} [a : DecidableEq V] [b : Fintype V] [Nonempty V]
    (F : CNF V) (order : DeclaredOrder V) {h d j r c e : ℕ}
    (base ell q prec kp bw : ℕ) (three : ∀ row∈F,row.length≤3)
    (large : binderDomain (headAtThree F order h d j r c e base ell q prec kp bw three))
    (positive : 0<ell)
    (words : binderDomain (headAtThree F order h d j r c e base ell q prec kp bw three large positive))
    (guards : @SerialGuards V a b F order h d j r c e)
    (code : V→List Bool) (inj : Function.Injective code)
    (declared : List (List Bool)) (body : BitsCNF)
    (declaredExact : declared=order.roster.map code) (bodyExact : body=codeCNF code F)
    (C : ℕ)
    (fit : base≤C*physicalSize (nWires (guardedInOrder F order.roster))
      (Paper6SourceSize.sourceNativeSize F order)) :
    let s := physicalSize (nWires (guardedInOrder F order.roster))
      (Paper6SourceSize.sourceNativeSize F order)
    let I := headAtThree F order h d j r c e base ell q prec kp bw three large positive words
      guards code inj declared body declaredExact bodyExact
    I.field.steps≤(searchConstant+32*C+5188)*s^8 := by
  change (paidFreshFieldFrame F order base).steps ≤ _
  exact (actual_root_field_is_generated_and_polynomial F order base C fit).2.2.2.2

#print axioms fresh_shared_field_is_actual_and_source_polynomial
end
end J6R108FreshFieldRate

