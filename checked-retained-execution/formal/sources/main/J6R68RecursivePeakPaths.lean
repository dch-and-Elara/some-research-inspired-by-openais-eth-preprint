import J6R66ActiveLedger
import J6R57LiveSpaceCachedStack
import J6R66BootPeakMount

/-! The proof adapter for active callbacks does not replace any physical,
raw, indexed, framed-cache or directory observations. Transport them
along the exact source-state and birth equalities, not a semantic equality
of the final returned value. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R51Peak J6R52Peak J6R52CacheWhole
open J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R66.BootPeak
open J6R63Active J6R64Active J6R66Active J6R49DFS
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4450
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 19000000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)


theorem same_source_objects_give_all_same_ingress_fields
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew)
    (B : PageBank f ell key prec tw bw page) (own : OwnsHeader E.header B)
    (p : Path sel r c) :
    let Q := shadow M F E B own
    physicalInputStackBits Q p=physicalInputStackBits M p ∧
    rawStackBits Q p=rawStackBits M p ∧
    addonStackBits Q p=addonStackBits M p ∧
    cacheStackBits Q p=cacheStackBits M p := by
  let Q := shadow M F E B own
  change physicalInputStackBits Q p=physicalInputStackBits M p ∧
    rawStackBits Q p=rawStackBits M p ∧ addonStackBits Q p=addonStackBits M p ∧
    cacheStackBits Q p=cacheStackBits M p
  induction p with
  | root => exact ⟨rfl,rfl,rfl,rfl⟩
  | step p w ih =>
    have h : sourceState Q p w=sourceState M p w :=
      shadow_stored_sites_unchanged M F E B own p w
    rcases ih with ⟨phys,raw,addon,cache⟩
    refine ⟨?_,?_,?_,?_⟩
    · simp only [physicalInputStackBits]
      rw [phys,h]
    · simp only [rawStackBits]
      rw [raw,h]
    · simp only [addonStackBits,sourceBankAt]
      rw [addon,h]
    · simp only [cacheStackBits,actualMountedFields,sourceMounted]
      rw [cache,h]

theorem same_source_ingress_and_directory
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew)
    (B : PageBank f ell key prec tw bw page) (own : OwnsHeader E.header B)
    (p : Path sel r c) :
    let Q := shadow M F E B own
    cachedIngressBits Q p=cachedIngressBits M p ∧
    stackBank (borns Q) B p=stackBank (borns M) B p := by
  let Q := shadow M F E B own
  obtain ⟨phys,raw,add,cache⟩ := same_source_objects_give_all_same_ingress_fields M F E B own p
  refine ⟨?_,?_⟩
  · change cachedIngressBits Q p=_
    unfold cachedIngressBits
    rw [phys,raw,add,cache]
  · change stackBank (borns Q) B p=_
    rw [shadow_births_unchanged M F E B own]

theorem same_actual_preparation_for_pause
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew)
    (B : PageBank f ell key prec tw bw page) (own : OwnsHeader E.header B)
    (p : Path sel r c) (a : (S).cutoff<c.edges) :
    activeAt (shadow M F E B own) p a=liveActiveAt M F E B own p a := by
  have eq : activeAt (shadow M F E B own) p a=preparedActive (shadow M F E B own) p a := by
    cases p <;> rfl
  exact eq.trans (local_schedule_reads_exact_active_preparation M F E B own p a)

#print axioms same_source_objects_give_all_same_ingress_fields
#print axioms same_source_ingress_and_directory
#print axioms same_actual_preparation_for_pause
end
end J6R68.RecursivePeak