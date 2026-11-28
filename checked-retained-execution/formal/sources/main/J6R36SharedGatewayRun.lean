import J6R36SharedGatewayRebase

/-! Start the real R34 continuation from the new, actually installed
R35 seed. Its checked identical immutable state, not a price analogy,
is what permits the exact same inherited data and continuation. -/
namespace J6R36SharedGateway
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R35GatewayPreparation J6R34OfficialGateway
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R22Active
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R9Recursive
open J6R10Reachable J6R12Blueprint J6R11Blueprint J6ActiveRun J6ActiveSchedule J1PPrinted
open J6R30ProducedGateRegistry J6R21Ancestor J6R31RootResidentTables
set_option maxHeartbeats 14500000
set_option maxRecDepth 2600
set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
variable (S : ActualRootPreparation G ell q)
variable (literal : S=(rootPreparationFor X).result)
variable (pad : ℕ) (A : AtlasJob X pad)

theorem seed_predicate (pad : ℕ) :
    IsLive (X.seed pad)=IsLive (preparedSeed X S literal pad) := by
  funext B
  exact propext (prepared_seed_same_live X S literal pad B).symm

noncomputable def cachedRoutes :
    RoutedInputs A.inputs (preparedSeed X S literal pad) :=
  rebaseRoutes (seed_predicate X S literal pad) A.inherited

noncomputable def cachedPlan :=
  compilerResident A.inputs (preparedSeed X S literal pad) (cachedRoutes X S literal pad A)

theorem cached_plan_is_literal :
    cachedPlan X S literal pad A=compilerResident A.inputs (X.seed pad) A.inherited :=
  same_anchored_resident (seed_predicate X S literal pad) A.inherited

theorem cached_ready :
    JobsReady A.bank (preparedSeed X S literal pad::
      (pagedLog (cachedPlan X S literal pad A) (askedJobChild X) .root).jobs) := by
  rw [cached_plan_is_literal X S literal pad A]
  exact jobs_ready_same_head_id A.bank (X.seed pad) (preparedSeed X S literal pad) _
    (same_seed_bytes X S literal pad).2.1 A.ready

noncomputable def runCached :
    Meter (Block (A.tree.frame (.reflexive (askedJobChild X))) ell×
      PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  startFromAtlas (cachedPlan X S literal pad A) (preparedSeed X S literal pad) A.bank

theorem actual_new_install_and_continuation :
    let j := preparedSeed X S literal pad
    let old := X.seed pad
    let tail := nativePaged (compilerResident A.inputs old A.inherited) (askedJobChild X) .root
    let out := runCached X S literal pad A
    (j.install A.bank).result=(old.install A.bank).result ∧
    out.result=A.run.result ∧
    out.steps=publishFee A.bank j.entry j.offset j.built+
      (tail (old.install A.bank).result.1).steps+4 ∧
    A.run.steps=publishFee A.bank old.entry old.offset old.built+
      (tail (old.install A.bank).result.1).steps+4 := by
  let j := preparedSeed X S literal pad
  let old := X.seed pad
  let P := compilerResident A.inputs old A.inherited
  let tail := nativePaged P (askedJobChild X) .root
  let bad : Meter (Block (A.tree.frame (.reflexive (askedJobChild X))) ell) :=
    zeroM (A.tree.frame (.reflexive (askedJobChild X))).hp
  have fresh : ∀ row∈A.bank.headers,row.id≠old.identifier :=
    A.ready.2.2 old List.mem_cons_self
  obtain ⟨states,fee⟩ := prepared_seed_exact_install X S literal pad A.bank A.ready.1 fresh
  have promised := (next_job_exact A.bank old (pagedLog P (askedJobChild X) .root).jobs A.ready).1
  have yes : (old.install A.bank).result.2=true :=
    congrArg (fun r=>r.result.2) promised
  have past : (old.install A.bank).steps=publishFee A.bank old.entry old.offset old.built :=
    congrArg Meter.steps promised
  obtain ⟨output,timeNew,timeOld⟩ :=
    same_published_continuation A.bank old j tail bad yes states
  refine ⟨states,?_,?_,?_⟩
  · unfold runCached
    rw [cached_plan_is_literal X S literal pad A]
    exact output
  · unfold runCached
    rw [cached_plan_is_literal X S literal pad A]
    exact timeNew.trans (by rw [show (j.install A.bank).steps=_ from fee])
  · exact timeOld.trans (by rw [past])

theorem cached_child_chronology [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    let j := preparedSeed X S literal pad
    let child := askedJobChild X
    let log := Log.enter j (pagedLog (cachedPlan X S literal pad A) child .root)
    let out := runCached X S literal pad A
    (A.tree.frame (.reflexive child)).decode out.result.1=
      reduce child.prec f ell (child.host.contract X.hf) ∧
    out.result.2=afterJobs A.bank log.jobs ∧
    out.steps=(reference A.tree child (.reflexive child)).steps+
      chronologicalBill A.bank log.jobs+log.extras A.bank := by
  letI : DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) (askedJobChild X)) :=
    sourceDecision (G.selector ell) (askedJobChild X)
  exact built_children_and_root_run A.inputs (preparedSeed X S literal pad)
    (cachedRoutes X S literal pad A) A.bank (cached_ready X S literal pad A)

noncomputable def cachedGroupReceipt [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    GroupReceipt (ell:=ell) G X.hf X.centre X.sample X.group where
  frame := A.tree.frame (.reflexive (askedJobChild X))
  run := ⟨(runCached X S literal pad A).result.1,(runCached X S literal pad A).steps⟩
  truth := (cached_child_chronology X S literal pad A).1

theorem cached_group_is_same_raw_result [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    (cachedGroupReceipt X S literal pad A).run.result=(receiptFromAtlas X pad A).run.result :=
  congrArg Prod.fst (actual_new_install_and_continuation X S literal pad A).2.1

include literal in
theorem cached_keeps_probe_frame_and_halves :
    S.frame=X.field.result ∧
    (∀ t : Fin (sampleCount f ell m base n native T),
      (S.probes.read t).result.val=AOracleMachineTimeTape.encodeBits f.natDegree (t.val+1)) ∧
    S.parents=(makeTypedRootParent G X.source ell X.centre).result.raw := by
  subst S
  refine ⟨rfl,?_,?_⟩
  · intro t
    exact ((build_root_probe_receipt G ell).2 t).1
  · exact (actual_shared_parent_file G X.source ell X.field X.hq X.copies X.pre X.centre).1

#print axioms seed_predicate
#print axioms cached_plan_is_literal
#print axioms cached_ready
#print axioms actual_new_install_and_continuation
#print axioms cached_child_chronology
#print axioms cached_group_is_same_raw_result
#print axioms cached_keeps_probe_frame_and_halves
end J6R36SharedGateway
