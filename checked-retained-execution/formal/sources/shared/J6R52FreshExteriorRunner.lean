import J6R52FreshExteriorMount
import J6R51LeafWhole

/-! The mounted raw source and the online interpreter use one and the
same actual exterior record. The local loader and positive-terminal
source interface are still explicit inputs. -/
namespace J6R52FreshExterior
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime J6R15ModeCost
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant J6R30GeneratedRootLayout
open J6R26StablePreparedRoot J6R34RootAtlas J6R27PrescribedProbe J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R20Ancestor J6R21Ancestor
open J6R12Blueprint J6R17ModeTape J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R51Ingress J6R49RootIngress J6R50RootIngress P11FullPacking
open J6R24LegalLayout J6R24MeteredRecursion
open J6ActiveRun J6R11Blueprint J6R10Reachable J6R26DescriptorTree J6R48DFS
open J6R50SourceProducer J6R51Online J6R51Leaf J6R50Leaf

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3600
set_option maxHeartbeats 18000000
set_option linter.unusedSectionVars false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

def mountedOnline (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
    {prep : Prepared G.bounds (G.selector ell) (exteriorChild G ell X.centre X.sample X.group) X.hf}
    [DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell))
      (exteriorChild G ell X.centre X.sample X.group))]
    (finder : OnlineMachine prep key prec tw bw (pageKeyWidth m+pad) rate)
    (bp : 0<base)
    (ordering : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
      (exteriorChild G ell X.centre X.sample X.group).host.Edge)
    (D : ∀ {ticket : Ticket (G.selector ell) (exteriorChild G ell X.centre X.sample X.group)}
      (site : StoredSite prep ticket key prec tw bw (pageKeyWidth m+pad)),ResidentLeafData site)
    (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :
    Meter (Block (prep.frame (Path.root : Path (G.selector ell)
      (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).reached) ell
        × PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  let mount := (X.seed pad).install initial
  let runner := replaceTerminalFields X pad finder bp ordering D
  let out := runRoot runner retire mount.result.1
  ⟨out.result,mount.steps+out.steps+4⟩

theorem mounted_online_reuses_the_new_source
    (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
    {prep : Prepared G.bounds (G.selector ell) (exteriorChild G ell X.centre X.sample X.group) X.hf}
    [DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell))
      (exteriorChild G ell X.centre X.sample X.group))]
    (finder : OnlineMachine prep key prec tw bw (pageKeyWidth m+pad) rate)
    (bp : 0<base)
    (ordering : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
      (exteriorChild G ell X.centre X.sample X.group).host.Edge)
    (D : ∀ {ticket : Ticket (G.selector ell) (exteriorChild G ell X.centre X.sample X.group)}
      (site : StoredSite prep ticket key prec tw bw (pageKeyWidth m+pad)),ResidentLeafData site)
    (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (leafChart : LoopCharts X pad finder bp D)
    (live : IsLive (X.seed pad) (((X.seed pad).install initial).result.1))
    (stack : ReadyOnStack (borns finder) (((X.seed pad).install initial).result.1)) :
    let ext := exteriorChild G ell X.centre X.sample X.group
    let A := mountedOnline X finder bp ordering D retire initial
    let job := (X.seed pad).install initial
    let run := runRoot (replaceTerminalFields X pad finder bp ordering D) retire job.result.1
    (prep.frame (Path.root : Path (G.selector ell) ext ext).reached).decode A.result.1 =
      (sourceBlueprint (G.selector ell) ext X.hf).program.run ext ∧
    A.result.2=job.result.1 ∧ A.steps=job.steps+run.steps+4 := by
  have E := actual_online_root_with_proved_terminal_fields X pad finder bp ordering D
    (((X.seed pad).install initial).result.1) live stack leafChart retire
  exact ⟨E.1,E.2,rfl⟩

#print axioms mountedOnline
#print axioms mounted_online_reuses_the_new_source
end
end J6R52FreshExterior
