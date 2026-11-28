import J6R58RequestSourceShell
import J6R53DispatchRawFields
import J6R57ScopeFeeAtlas

/-! Trace the exact code through the current source constructor, its
cached reader, and the genuinely published immutable packet. No
re-encoding of installed ancestor data occurs. -/
namespace J6R88ScopeCode
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R24MeteredRecursion
open J6R26DescriptorTree J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R34RootAtlas J6R33GeneratedChildSite J6R30ProducedGateRegistry
open J6R12Blueprint J6R11Blueprint J1PPrinted J6ActiveRun J6R16ModeCost
open J6R48RawRoute J6R50SourceProducer J6R51Online J6R52Dispatch J6R53Dispatch J6R58RequestSource

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4350
set_option maxHeartbeats 19000000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}
variable {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}
variable {U : ExplicitSelectedWords X.site w q} (R : Replayed X.site w q U)

theorem local_shell_uses_offered_numeric_code
    (body : Meter (LoadedPlane X R))
    (fitDepth : v.child.depth+1<2^X.input.dep)
    (fitPrec : (successorTicket v w).child.prec<2^prec) :
    let B := localFixedShell X R body fitDepth fitPrec
    B.result.code=body.result.code ∧ B.result.context=body.result.context :=
  ⟨rfl,rfl⟩

theorem raw_loaded_occurrence_uses_exact_shell_code
    (B : PayloadShell R) (D : DirectorySeed R B)
    {raw : List (Word (q+1))} (E : RawFields R raw) :
    (E.load B D).result.advance.next.input.code=B.code := rfl

theorem descended_source_state_uses_actual_demand_code
    (M : OnlineMachine T key prec tw bw page rate)
    (p : Path sel r c) (u : (Plan sel).Slot c)
    (w : (Plan sel).Slot ((Plan sel).child c u)) :
    (sourceState M (.step p u) w).input.code=(M.demand (sourceState M p u) w).result.event.code := rfl

theorem all_path_code_cap_iff_literal_first_and_demand
    (M : OnlineMachine T key prec tw bw page rate) (limit : ℕ) :
    (∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
      (sourceState M p w).input.code≤limit) ↔
    (∀ w : (Plan sel).Slot r,(M.initial w).result.input.code≤limit) ∧
      (∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (u : (Plan sel).Slot x)
        (w : (Plan sel).Slot ((Plan sel).child x u)),
        (M.demand (sourceState M p u) w).result.event.code≤limit) := by
  constructor
  · intro h
    refine ⟨fun w=>h .root w,?_⟩
    intro x p u w
    exact h (.step p u) w
  · intro h x p w
    cases p with
    | root => exact h.1 w
    | step p u => exact h.2 p u w

private theorem cast_birth_code_context {a b : ℕ} (eq : a=b)
    (x : Birth T v key prec tw bw a) :
    (eq ▸ x : Birth T v key prec tw bw b).job.immutable.payload.context=x.ctx := by
  cases eq
  rfl

theorem published_ancestor_reads_its_creation_code
    (I : OccurrenceInput T v key prec tw bw page) :
    let ctx := (compileOccurrence I).job.immutable.payload.context
    ctx=I.words.result.context ∧ (readContext ctx).result.2=I.code := by
  let A := Classical.choice (occurrence_real_receipt I)
  let issued := A1R12.padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)
  let B := issuedBirth I.native.result issued I.words.result I.hOld A
  have copied : (compileOccurrence I).job.immutable.payload.context=I.words.result.context :=
    cast_birth_code_context I.width B
  refine ⟨copied,?_⟩
  rw [copied,read_context_exact]
  exact I.codeExact

private theorem cast_birth_keeps_compile_bill {a b : ℕ} (eq : a=b)
    (x : Birth T v key prec tw bw a) :
    (eq ▸ x : Birth T v key prec tw bw b).compilePages.steps=x.compilePages.steps := by
  cases eq
  rfl

theorem actual_atlas_build_really_writes_full_numeric_code
    (I : OccurrenceInput T v key prec tw bw page) :
    3*I.code≤(compileOccurrence I).compilePages.steps := by
  let d := ticketReady T v
  let A := Classical.choice (occurrence_real_receipt I)
  let issued := A1R12.padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)
  let B := issuedBirth I.native.result issued I.words.result I.hOld A
  have words : I.words.result.exponents.length=I.geometry.modes.length := by
    simpa only [List.length_map] using congrArg List.length I.acted
  have hPrepare := prepare_site_exact (code:=I.code) I.geometry I.words.result I.clock words
  have bill : 3*I.code≤(prepareSite I.code I.physical.result I.words.result).steps := by
    rw [hPrepare]
    change 3*I.code≤prepareSiteFee ((printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth)
      I.q (centerIndex d v.centerAt).val I.fw.length I.code tw bw I.geometry.modes.length
    unfold prepareSiteFee
    omega
  have keeps : (compileOccurrence I).compilePages.steps=B.compilePages.steps :=
    cast_birth_keeps_compile_bill I.width B
  rw [keeps]
  change 3*I.code≤(runSiteRows (code:=I.code) I.physical.result I.words.result
    (register_positive d v.centerAt) I.outerPos I.fit).steps
  unfold runSiteRows runSiteAtlas
  dsimp only
  split
  · dsimp only
    omega
  · dsimp only
    omega

#print axioms local_shell_uses_offered_numeric_code
#print axioms raw_loaded_occurrence_uses_exact_shell_code
#print axioms descended_source_state_uses_actual_demand_code
#print axioms all_path_code_cap_iff_literal_first_and_demand
#print axioms published_ancestor_reads_its_creation_code
#print axioms actual_atlas_build_really_writes_full_numeric_code
end
end J6R88ScopeCode
