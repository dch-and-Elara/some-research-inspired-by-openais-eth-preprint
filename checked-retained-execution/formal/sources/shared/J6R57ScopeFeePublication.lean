import J6R51PeakFeeBound
import J6R51PeakOnlineDirectory

/-! Width- and lifetime-based publication charge for each actual
source occurrence. In particular neither an extra offset cap nor
a bound on the number of future sibling jobs is supplied. -/
namespace J6R57ScopeFee
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS J6R50SourceProducer J6R50Peak J6R51Peak J6R51Online
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4800
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def liveHeaderWidth (rootEdges fixed addr body initialWidth : ℕ) : ℕ :=
  max initialWidth (fixed+(3*rootEdges/29)*(addr+body))

def livePublicationSetup (s C rootEdges key prec tw bw fixed addr body initialWidth
    initialHeaders initialRecords : ℕ) : ℕ :=
  publicationOverhead key prec tw bw fixed (liveHeaderWidth rootEdges fixed addr body initialWidth)
    (initialHeaders+pathLimit s C) (initialRecords+pathLimit s C)

theorem publication_overhead_mono_offset_counts (key prec tw bw width : ℕ)
    {a b h H k K : ℕ} (offset : a≤b) (heads : h≤H) (refs : k≤K) :
    publicationOverhead key prec tw bw a width h k≤
      publicationOverhead key prec tw bw b width H K := by
  have scan := Nat.mul_le_mul_right (12*key+3*width+12) heads
  have locate := Nat.mul_le_mul_right (13*key+13) refs
  unfold publicationOverhead scanByWidth headerReadFee locateFee
  omega

theorem birth_offset_le_fixed_words {v : Ticket sel r}
    (b : Birth T v key prec tw bw page) : b.job.offset≤fixedWords b := by
  change b.tc+(b.tz+(b.tm+6))≤b.tc+(b.tz+(b.tm+6))+prec+b.dep+b.edge
  omega

theorem birth_paged_fee_is_real_compile {v : Ticket sel r} (b : Birth T v key prec tw bw page) :
    b.job.built.steps=b.compilePages.steps+shapeFrameFee prec := by
  change (packPages b.shape b.compilePages).steps=_
  exact congrArg Meter.steps (packed_pages_exact b.shape b.compilePages b.rows b.success)

theorem actual_scope_publish_has_word_and_depth_ceiling
    (M : OnlineMachine T key prec tw bw page q) (initial : L)
    (fixed addr seed U : ℕ) (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (initialFit : ∀ row∈initial.headers,row.bytes.length≤U)
    (p : Path sel r c) (w : (P).Slot c) :
    let b := borns M p w
    let bank := stackBank (borns M) initial p
    publishFee bank b.job.entry b.job.offset b.job.built≤
      b.job.entry.steps+b.compilePages.steps+shapeFrameFee prec+
        livePublicationSetup s C r.edges key prec tw bw fixed addr (sourceBodyCap s C seed) U
          initial.headers.length initial.records.length := by
  let b := borns M p w
  let bank := stackBank (borns M) initial p
  let W := liveHeaderWidth r.edges fixed addr (sourceBodyCap s C seed) U
  have fit : SourceHeaderFit (borns M) fixed addr (sourceBodyCap s C seed) := by
    intro x z u
    exact geometry_of_real_demand_caps_the_raw_header M fixed addr seed sizes boot z u
  have caps : ∀ row∈bank.headers,row.bytes.length≤W :=
    live_headers_fit_same_geometric_cap (borns M) initial fixed addr (sourceBodyCap s C seed) fit U initialFit p
  have next : b.job.entry.result.bytes.length≤W :=
    (next_descriptor_fits_geometric_cap (borns M) fixed addr (sourceBodyCap s C seed) fit p w).trans (le_max_right _ _)
  have a := actual_publication_fee_with_explicit_word_caps bank b.job W caps next
  have d := actual_ancestry_moves_any_start cfg sel T.rootStable p
  obtain ⟨hs,rs⟩ := stack_directory_size (borns M) initial p
  have bOffset : b.job.offset≤fixed := (birth_offset_le_fixed_words b).trans (sizes p w).1
  have hHead : bank.headers.length ≤ initial.headers.length+pathLimit s C := by
    change (stackBank (borns M) initial p).headers.length ≤ _
    rw [hs]
    exact Nat.add_le_add_left d initial.headers.length
  have hRef : bank.records.length ≤ initial.records.length+pathLimit s C := by
    change (stackBank (borns M) initial p).records.length ≤ _
    rw [rs]
    exact Nat.add_le_add_left d initial.records.length
  have hOver := publication_overhead_mono_offset_counts key prec tw bw W bOffset hHead hRef
  have price : b.job.built.steps=b.compilePages.steps+shapeFrameFee prec := birth_paged_fee_is_real_compile b
  change publishFee bank b.job.entry b.job.offset b.job.built≤_
  calc
    _≤b.job.entry.steps+b.job.built.steps+
        publicationOverhead key prec tw bw b.job.offset W bank.headers.length bank.records.length := a
    _=b.job.entry.steps+b.compilePages.steps+shapeFrameFee prec+
        publicationOverhead key prec tw bw b.job.offset W bank.headers.length bank.records.length := by
      simp only [price,Nat.add_assoc]
    _≤_ := Nat.add_le_add_left hOver _

end
#print axioms publication_overhead_mono_offset_counts
#print axioms birth_offset_le_fixed_words
#print axioms birth_paged_fee_is_real_compile
#print axioms actual_scope_publish_has_word_and_depth_ceiling
end J6R57ScopeFee
