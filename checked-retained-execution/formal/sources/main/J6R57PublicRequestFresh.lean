import J6R57PublicRequestCache
import J6R54PublicFamilyFresh

/-! Specialize the common request inputs to the deterministic guarded
raw input serializer and the checked selected field.  Width and
source-shape guards remain explicit, not per-query supplied recipes. -/
namespace J6R57PublicRequest
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R51Ingress
open J6R49RootIngress J6R50RootIngress J6R52FreshShape J6R52FreshExterior J6R15ModeCost
open J6R54PublicFamily J6R14ZeroMode J6R34RootAtlas J6R27PrescribedProbe
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22000000
set_option maxRecDepth 4200
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R51Ingress.freshPlant J6R51Ingress.guardedInOrder
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (F : CNF V) (O : DeclaredOrder V)
variable {h d j r c e base ell q prec kp bw tc tj tw edgew : ℕ}
variable (three : ∀ row∈F,row.length≤3)
variable (large : printedGuard (nWires (guardedInOrder F O.roster)) (Paper6SourceSize.sourceNativeSize F O))
variable (positive : 0<ell)
variable (A : FreshWords (nWires (guardedInOrder F O.roster)) base q prec kp bw)
variable (guard : SerialGuards F O h d j r c e)
variable (name : V→List Bool) (inj : Function.Injective name)
variable (declared : List (List Bool)) (body : BitsCNF)
variable (declaredExact : declared=O.roster.map name) (bodyExact : body=codeCNF name F)
variable (W : Widths (nWires (guardedInOrder F O.roster))
  (Paper6SourceSize.sourceNativeSize F O) tc tj tw edgew)

def compileRawRequestCatalogue :=
  let I := freshSharedInputs F O base ell q prec kp bw three large positive A guard
    name inj declared body declaredExact bodyExact
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F O).f)) :=
    ⟨(generated_fresh_field_is_permitted F O).2⟩
  compileRequestInputs W I

theorem actual_guarded_raw_table_complete :
    let J := compileRawRequestCatalogue F O three large positive A guard name inj declared body
      declaredExact bodyExact W
    let m := nWires (guardedInOrder F O.roster)
    let n := Paper6SourceSize.sourceNativeSize F O
    J.result.requests.rows.length=(m+1)*(literalDegree m n+1)*64 ∧
      J.result.requests.probes=J.result.root.probes := by
  dsimp only
  refine ⟨?_,rfl⟩
  exact (catalogue_exact_order_and_bill W A.mark).2.1

#print axioms compileRawRequestCatalogue
#print axioms actual_guarded_raw_table_complete
end
end J6R57PublicRequest
