import J6R111FreshStartupBinding

/-! Evaluation on the very image returned from the paid original startup.
The dependent image type binds the marker, concrete compiler output and
installed request inputs to the same original source input. -/
namespace J6R112ExecutedSelectedStartup
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R51Ingress
open J6R49RootIngress J6R50RootIngress J6R52FreshShape J6R52FreshExterior J6R15ModeCost
open J6R27PrescribedProbe J6R54PublicFamily J6R57PublicRequest
open J6R110RootWidthChoice J6R110RequestWidthChoice J6R111FreshStartupBinding

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 3700
set_option maxHeartbeats 10000000

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {order : DeclaredOrder V}
local notation "Graph" => (guardedInOrder F order.roster)
local notation "m" => (nWires Graph)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)
local notation "s" => (physicalSize m n)
variable {h d j r c e base ell kp : ℕ}
variable (A : RawStartup F order h d j r c e base ell kp)

abbrev StartupImage (fit : base ≤ s ^ 2) :=
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  RequestImage (chooseWidths m n (fresh_source_native_fits F order))
    (originalInputsAtGeneratedWords A (initialPaidWords A fit).result)

/-- The continuation receives the paid payload, not new input from which to
manufacture another image. The two `Meter` debits are included once each. -/
def usingActualImage (fit : base ≤ s ^ 2) {B : Type*}
    (continuation : StartupImage A fit → Meter B) : Meter B :=
  let startup := selectedStartup A fit
  let used := continuation startup.result
  ⟨used.result, startup.steps + used.steps⟩

theorem one_actual_startup_result_and_debit (fit : base ≤ s ^ 2) {B : Type*}
    (continuation : StartupImage A fit → Meter B) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let words := initialPaidWords A fit
    let source := originalInputsAtGeneratedWords A words.result
    let W := chooseWidths m n (fresh_source_native_fits F order)
    let built := buildRequestImage W source
    let used := continuation (selectedStartup A fit).result
    usingActualImage A fit continuation =
      ⟨used.result, ordinalFee (chosenQ m) base + built.steps + used.steps⟩ := by
  dsimp only [usingActualImage]
  rw [(same_request_image_and_one_real_width_emission A fit).2]

#print axioms usingActualImage
#print axioms one_actual_startup_result_and_debit
end
end J6R112ExecutedSelectedStartup

