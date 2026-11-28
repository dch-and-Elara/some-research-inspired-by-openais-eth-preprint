import J6R55PublicOrderCore
import J6R55PublicReserve

/-! The root chart uses the physical port list emitted by
makeTypedRootParent for the same literal R54 site and the same raw
group word consumed by its existing header. A separately read key
book pays both scans; mount's existing header scan is not rewritten. -/
namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R14ZeroMode J6R27PrescribedProbe
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs J6R54PublicFamily
open J6R25PreparedSupply J6R34ChildPath J6R15ModeCost
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R52FreshExterior
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 19000000
set_option maxRecDepth 3700
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {A : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) A (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)

def publicExteriorOrder :
    Fin (exteriorChild G ell i j g).edges≃(exteriorChild G ell i j g).host.Edge :=
  let X := literalSite W C i j g
  let P := makeTypedRootParent G X.source ell X.centre
  externalEdgeOrder P.result X.group (rootPreset G ell) X.sample

def publicExteriorKeyTape : Meter (List (Word (rootHalfWidth m))) :=
  let X := literalSite W C i j g
  let P := makeTypedRootParent G X.source ell X.centre
  let O := selectedEdgeBook X.address.group P.result.raw
  ⟨O.result,P.steps+O.steps+4⟩

theorem actual_public_key_book_in_its_own_order :
    let X := literalSite W C i j g
    let P := makeTypedRootParent G X.source ell X.centre
    let R := publicExteriorKeyTape W C i j g
    R.result=List.ofFn (fun k=>externalEdgeKey P.result X.group (rootPreset G ell) X.sample
      (publicExteriorOrder W C i j g k)) ∧ R.result.Nodup ∧
      R.steps≤P.steps+7+(P.result.raw.map rowScanFee).sum+
        (exteriorChild G ell i j g).edges*(4*rootHalfWidth m+5)+4 := by
  let X := literalSite W C i j g
  let P := makeTypedRootParent G X.source ell X.centre
  let O := selectedEdgeBook X.address.group P.result.raw
  have H := actual_external_edge_key_book P.result X.group (rootPreset G ell) X.sample X.address.group X.groupOK
  refine ⟨H.1,H.2.1,?_⟩
  have fee := H.2.2
  change P.steps+O.steps+4≤P.steps+7+(P.result.raw.map rowScanFee).sum+
    (exteriorChild G ell i j g).edges*(4*rootHalfWidth m+5)+4
  change O.steps≤7+(P.result.raw.map rowScanFee).sum+
    (exteriorChild G ell i j g).edges*(4*rootHalfWidth m+5) at fee
  simpa only [Nat.add_assoc] using Nat.add_le_add_right (Nat.add_le_add_left fee P.steps) 4

#print axioms publicExteriorOrder
#print axioms publicExteriorKeyTape
#print axioms actual_public_key_book_in_its_own_order
end
end J6R55Public

