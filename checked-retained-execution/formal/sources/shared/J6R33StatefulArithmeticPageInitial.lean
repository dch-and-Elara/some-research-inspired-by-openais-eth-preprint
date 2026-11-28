import J6R33StatefulArithmeticPageWhole

/-! Optional paid outside-root arrival. This is one real initial
publication, not a prepass over descendant births. Its output directory
is the unique input of the whole dynamic paged evaluator. -/
namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime A1R10 J6R22Active J6ActiveRun J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

noncomputable def startFromAtlas (R : PagedResident T key prec tw bw page) (seed : J) :
    SM L (Block (T.frame (.reflexive r)) ell) :=
  withPublished seed (nativePaged R r .root) (zeroM (T.frame (.reflexive r)).hp)

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem installed_atlas_starts_root (R : PagedResident T key prec tw bw page) (seed : J)
    (anchor : ∀ B,IsLive seed B→R.rootLive B)
    (B : L) (ready : JobsReady B (seed::(pagedLog R r .root).jobs)) :
    let out := startFromAtlas R seed B
    let log := Log.enter seed (pagedLog R r .root)
    (T.frame (.reflexive r)).decode out.result.1=(sourceBlueprint sel r hf).program.run r ∧
      out.result.2=afterJobs B log.jobs ∧
      out.steps=(reference T r (.reflexive r)).steps+chronologicalBill B log.jobs+log.extras B := by
  let F := T.frame (.reflexive r)
  have recursiveRun := paged_follows R r (.root)
  have live : ∀ bank : L,JobsReady bank (seed::(pagedLog R r .root).jobs)→True→
      opened R.births R.rootLive (Path.root (sel:=sel) (r:=r)) (afterOne bank seed) :=
    fun bank _ _=>anchor _ (new_is_live seed bank)
  have h := enter_traced (P:=fun _=>True) seed (nativePaged R r .root) (zeroM F.hp)
    (reference T r (.reflexive r)) (pagedLog R r .root).jobs (pagedLog R r .root).extras live recursiveRun
  obtain ⟨word,bank,fee⟩ := h B ready True.intro
  exact ⟨(congrArg F.decode word).trans (reference_source T r (.reflexive r)),bank,fee⟩

#print axioms installed_atlas_starts_root
end J6R33StatefulArithmeticPage
