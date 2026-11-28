import J6R34RootAtlasOccurrence
import J6R33StatefulArithmeticPageInitial

/-! Attach the measured descendant compiler directly to the R33 tree.
Consequently the resident plan does not carry arbitrary completed page
capsules. The inductive port-routing invariant and issued-key legality
remain explicit. -/
namespace J6R34RootAtlas
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6R26DescriptorTree J6R24MeteredRecursion J6R12Blueprint J6R11Blueprint J6R10Reachable
open J6ActiveRun J6ActiveSchedule J6R9Recursive J1PPrinted J6R20Ancestor J6R10Repack
open J6R21Ancestor J6R16ModeCost

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

structure RoutedInputs (actual : InputFamily T key prec tw bw page) (seed : J) where
  leaf : ∀ {c : Call (PhysicalHost f ell)},Path sel r c→c.edges≤(SP).cutoff→PagedLeaf c key page
  route : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (stop : c.edges≤(SP).cutoff)
    (B : PageBank f ell key prec tw bw page),
    opened (compileFamily actual) (IsLive seed) p B→∀ (x : Fin c.edges→Bool) v,
      (T.frame p.reached).decode ((leaf p stop).query hf (T.frame p.reached) T.vPositive B v (List.ofFn x)).result=
        (c.host.file v).read hf c.prec
          (assignment c.host.network (x∘c.host.edgeOrder c.edges (leaf p stop).sameEdges) v)

noncomputable def compilerResident (actual : InputFamily T key prec tw bw page) (seed : J)
    (physical : RoutedInputs actual seed) : PagedResident T key prec tw bw page :=
  ⟨compileFamily actual,IsLive seed,live_monotone seed,physical.leaf,physical.route⟩

variable [eqs : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem fixed_source_value (T : Prepared cfg sel r hf) :
    (sourceBlueprint sel r hf).program.run r=reduce r.prec f ell (r.host.contract hf) := by
  have e : eqs=sourceDecision sel r := Subsingleton.elim _ _
  subst eqs
  letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) := sourceDecision sel r
  let F := T.frame (.reflexive r)
  have earlier : 0<f.natDegree := F.natDegree hf ▸ F.sizePos
  exact J6R12Integral.printed_run_exact cfg sel r T.rootStable hf earlier

theorem built_children_and_root_run
    (actual : InputFamily T key prec tw bw page) (seed : J)
    (physical : RoutedInputs actual seed) (B : L)
    (legal : JobsReady B (seed::(pagedLog (compilerResident actual seed physical) r .root).jobs)) :
    let P := compilerResident actual seed physical
    let log := Log.enter seed (pagedLog P r .root)
    let out := startFromAtlas P seed B
    (T.frame (.reflexive r)).decode out.result.1=reduce r.prec f ell (r.host.contract hf) ∧
      out.result.2=afterJobs B log.jobs ∧
      out.steps=(reference T r (.reflexive r)).steps+chronologicalBill B log.jobs+log.extras B := by
  obtain ⟨word,state,cost⟩ := installed_atlas_starts_root (compilerResident actual seed physical) seed
    (fun _ h=>h) B legal
  exact ⟨word.trans (fixed_source_value T),state,cost⟩

#print axioms fixed_source_value
#print axioms built_children_and_root_run
end J6R34RootAtlas
