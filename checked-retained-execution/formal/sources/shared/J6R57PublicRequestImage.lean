import J6R57PublicRequestCache

/-! Store the compiled value itself next to its dependent request
tables.  A caller can borrow the actual compiled value; it need not
run `prepareShared I` again merely to recover a type parameter. -/
namespace J6R57PublicRequest
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4100
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

structure RequestImage
    (W : Widths m native tc tj tw edgew)
    (I : SharedInputs G ell q rr cc dd prec kp bw) where
  compiled : Compiled G ell q rr cc dd prec kp bw
  exactCompiled : compiled=(prepareShared I).result
  tables : InstalledRequestInputs W compiled

variable (W : Widths m native tc tj tw edgew) (I : SharedInputs G ell q rr cc dd prec kp bw)

def buildRequestImage : Meter (RequestImage W I) :=
  let C := prepareShared I
  let D := buildRequestInputs C.result W
  ⟨⟨C.result,rfl,D.result⟩,C.steps+D.steps+3⟩

theorem actual_request_image_retains_paid_compilation :
    let S := buildRequestImage W I
    S.result.compiled.literal=I.literal.result ∧ S.result.compiled.frame=I.field.result ∧
      S.result.tables.requests.probes=S.result.tables.root.probes ∧
      S.result.tables.requests.rows=(emitCatalogue W I.mark).result ∧
      S.steps=(compileRequestInputs W I).steps :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem actual_request_image_row_count :
    (buildRequestImage W I).result.tables.requests.rows.length=
      (m+1)*(literalDegree m native+1)*64 :=
  (catalogue_exact_order_and_bill W I.mark).2.1

#print axioms actual_request_image_retains_paid_compilation
#print axioms actual_request_image_row_count
end
end J6R57PublicRequest
