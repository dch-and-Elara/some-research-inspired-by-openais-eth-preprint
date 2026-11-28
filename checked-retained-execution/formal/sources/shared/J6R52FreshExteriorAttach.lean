import J6R52FreshExteriorSetup
import J6R51IngressSerialConsumers

/-! Exact literal source taken from the raw CNF serializer, not from
a prechosen historical chart. -/
namespace J6R52FreshExterior
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime J6R15ModeCost
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant J6R30GeneratedRootLayout
open J6R26StablePreparedRoot J6R34RootAtlas J6R27PrescribedProbe J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R20Ancestor J6R21Ancestor
open J6R12Blueprint J6R17ModeTape J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R51Ingress J6R49RootIngress J6R50RootIngress J6R24LegalLayout J6R24MeteredRecursion

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3000
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false

noncomputable section
theorem raw_port_file_attaches_to_real_exterior
    {V : Type} [DecidableEq V] [Fintype V]
    (F : CNF V) (order : DeclaredOrder V) {f : ℤ[X]} {base native : ℕ}
    {G : RootShape f (nWires (guardedInOrder F order.roster)) (printedHalf (nWires (guardedInOrder F order.roster))) base native (printedRankWidth (nWires (guardedInOrder F order.roster)))
      (freshPlant (guardedInOrder F order.roster) (guardRoster order)) (J6R28GeneratedRootFrame.constantRootWord (nWires (guardedInOrder F order.roster)))}
    {ell q rr cc dd edgew tc tj key prec tw bw h j e : ℕ}
    (cfg : Setup G ell q edgew tc tj key prec tw bw)
    (guards : SerialGuards F order h dd j rr cc e)
    (code : V→List Bool) (inj : Function.Injective code)
    (fits : 1+(writeResidents (nWires (guardedInOrder F order.roster)) cfg.hq (oddAxis (nWires (guardedInOrder F order.roster))) cfg.copies cfg.pre
      (List.ofFn (plantHalfPort (freshPlant (guardedInOrder F order.roster) (guardRoster order)) (freshCodec (guardedInOrder F order.roster) (guardRoster order) rr cc dd guards.rowFit guards.columnFit guards.portFit)))).result.roster.modes.length<2^cfg.code) :
    ∃ (file : SerializedFrame rr cc dd)
      (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw),
      (serializeRawCNF (r:=rr) (c:=cc) (d:=dd) h j (order.roster.map code) (codeCNF code F)).result=some file ∧ X.source.codec=(freshCodec (guardedInOrder F order.roster) (guardRoster order) rr cc dd guards.rowFit guards.columnFit guards.portFit) ∧ X.source.raw=file.ports ∧
      X.centre=cfg.centre ∧ X.sample=cfg.sample ∧ X.group=cfg.group ∧ X.issue=cfg.issue := by
  obtain ⟨file,run,_,ports,_⟩ := serialized_actual_fresh_input F order code inj h dd j rr cc 0 e
    guards.hpos guards.dpos guards.jpos guards.rpos guards.cpos guards.clausesFit
    guards.rawLegFit guards.localsFit guards.edgesFit guards.rowFit guards.columnFit guards.portFit
  let source : LiteralPortFile (freshPlant (guardedInOrder F order.roster) (guardRoster order)) rr cc dd := ⟨(freshCodec (guardedInOrder F order.roster) (guardRoster order) rr cc dd guards.rowFit guards.columnFit guards.portFit),file.ports,ports⟩
  have range : 1+(writeResidents (nWires (guardedInOrder F order.roster)) cfg.hq (oddAxis (nWires (guardedInOrder F order.roster))) cfg.copies cfg.pre
      source.raw).result.roster.modes.length<2^cfg.code := by
    change 1+(writeResidents (nWires (guardedInOrder F order.roster)) cfg.hq (oddAxis (nWires (guardedInOrder F order.roster))) cfg.copies cfg.pre file.ports).result.roster.modes.length<2^cfg.code
    rw [ports]
    exact fits
  exact ⟨file,attachLiteral cfg source range,run,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms raw_port_file_attaches_to_real_exterior
end
end J6R52FreshExterior
