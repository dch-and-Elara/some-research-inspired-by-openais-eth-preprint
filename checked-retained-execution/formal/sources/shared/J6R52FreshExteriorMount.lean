import J6R52FreshExteriorAttach

/-! Mount the literal fresh serializer output in the actual exterior
source registry, with the new chart's exact physical page identifiers. -/
namespace J6R52FreshExterior
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime J6R15ModeCost
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant J6R30GeneratedRootLayout
open J6R26StablePreparedRoot J6R34RootAtlas J6R27PrescribedProbe J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R20Ancestor J6R21Ancestor
open J6R12Blueprint J6R17ModeTape J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R51Ingress J6R49RootIngress J6R50RootIngress P11FullPacking
open J6R24LegalLayout J6R24MeteredRecursion

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3300
set_option maxHeartbeats 12500000
set_option linter.unusedSectionVars false

noncomputable section

def continueWithFile {A B : Type} (load : Meter (Option A))
    (go : ∀ x, load.result=some x→Meter B) : Meter (Option B) :=
  match h : load.result with
  | none => ⟨none,load.steps+2⟩
  | some x =>
    let out := go x h
    ⟨some out.result,load.steps+out.steps+4⟩

theorem continue_actual_file_exact {A B : Type} (load : Meter (Option A))
    (go : ∀ x, load.result=some x→Meter B) (a : A) (h : load.result=some a) :
    continueWithFile load go=⟨some (go a h).result,load.steps+(go a h).steps+4⟩ := by
  cases load with
  | mk result steps =>
    change result=some a at h
    subst result
    rfl

theorem raw_attachment_is_live_at_the_exact_exterior_page
    {V : Type} [DecidableEq V] [Fintype V]
    (F : CNF V) (order : DeclaredOrder V) {f : ℤ[X]} {base native : ℕ}
    {G : RootShape f (nWires (guardedInOrder F order.roster)) (printedHalf (nWires (guardedInOrder F order.roster))) base native (printedRankWidth (nWires (guardedInOrder F order.roster)))
      (freshPlant (guardedInOrder F order.roster) (guardRoster order)) (J6R28GeneratedRootFrame.constantRootWord (nWires (guardedInOrder F order.roster)))}
    {ell q rr cc dd edgew tc tj key prec tw bw h j e : ℕ}
    (cfg : Setup G ell q edgew tc tj key prec tw bw)
    (guards : SerialGuards F order h dd j rr cc e)
    (code : V→List Bool) (inj : Function.Injective code)
    (fits : 1+(writeResidents (nWires (guardedInOrder F order.roster)) cfg.hq (oddAxis (nWires (guardedInOrder F order.roster))) cfg.copies cfg.pre
      (List.ofFn (plantHalfPort (freshPlant (guardedInOrder F order.roster) (guardRoster order)) (freshCodec (guardedInOrder F order.roster) (guardRoster order) rr cc dd guards.rowFit guards.columnFit guards.portFit)))).result.roster.modes.length<2^cfg.code)
    (pad : ℕ) (B : PageBank f ell key prec tw bw (pageKeyWidth (nWires (guardedInOrder F order.roster))+pad))
    (probePage : Page (a (nWires (guardedInOrder F order.roster))) (K (nWires (guardedInOrder F order.roster))) (Fin 64))
    (sync : B.synced) (fresh : ∀ row∈B.headers,row.id≠cfg.issue.result) :
    ∃ (file : SerializedFrame rr cc dd)
      (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw),
      (serializeRawCNF (r:=rr) (c:=cc) (d:=dd) h j (order.roster.map code) (codeCNF code F)).result=some file ∧ X.source.raw=file.ports ∧
      X.centre=cfg.centre ∧ X.sample=cfg.sample ∧ X.group=cfg.group ∧
      (X.seed pad).identifier=cfg.issue.result ∧
      ((X.seed pad).install B).result.2=true ∧
      IsLive (X.seed pad) (((X.seed pad).install B).result.1) ∧
      ∀ k : Page (a (nWires (guardedInOrder F order.roster))) (K (nWires (guardedInOrder F order.roster))) (Fin 64),
        (locate (widened pad (residentPageKey (nWires (guardedInOrder F order.roster)) k)).result
          (X.seed pad).immutable.payload.payload.pages).result=some (X.chosenFields k) := by
  obtain ⟨file,X,out,_,literalBytes,i,k,g,iss⟩ :=
    raw_port_file_attaches_to_real_exterior F order cfg guards code inj fits
  have legal : ∀ row∈B.headers,row.id≠X.issue.result := by
    rw [iss]
    exact fresh
  have receipt (p : Page (a (nWires (guardedInOrder F order.roster))) (K (nWires (guardedInOrder F order.roster))) (Fin 64)) :=
    true_exterior_seed_lookup X pad B sync legal p
  have E := receipt probePage
  refine ⟨file,X,out,literalBytes,i,k,g,E.2.2.1.trans (congrArg (fun y=>y.result) iss),
    E.1,E.2.1,?_⟩
  intro t
  exact (receipt t).2.2.2.1

#print axioms continueWithFile
#print axioms continue_actual_file_exact
#print axioms raw_attachment_is_live_at_the_exact_exterior_page
end
end J6R52FreshExterior
