
import J6R51PeakStack
import J6R51PeakInstallTrace
import J6R50PeakAbsolute

/-! Combined selected budget on the very same prepared native run
and absolute source path. Permanent non-page directory fields are
disjoint in the encoding from R50's page fields. During the next
publication, working copy buffers are counted once, at that operation,
not once at each suspended ancestor. -/
namespace J6R51Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits J6R50Peak

set_option autoImplicit false
set_option maxHeartbeats 16500000
set_option maxRecDepth 3550

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def pendingPageBits (j : J) : ℕ :=
  match j.built.result with
  | none => 0
  | some e => ((envelopePages e).map List.length).sum

theorem true_queued_pages_are_exact_increment (B : L) (j : J) :
    residentAtlasBits (afterOne B j)=residentAtlasBits B+pendingPageBits j := by
  unfold pendingPageBits
  rw [j.validBody]
  change (((envelopePages j.expected).map List.length).sum + residentAtlasBits B)=_
  exact Nat.add_comm _ _

theorem same_scoped_ancestry_with_resident_descriptors
    (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (qFit : q≤uniformWidth s C) (pageBound fixed port body : ℕ)
    (rows : AllExactPages R.births) (fields : SourceHeaderFit R.births fixed port body)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (path : Path sel r x) (w : (Plan sel).Slot x),
      let e := (R.births path w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound)
    (p : Path sel r c) :
    ∃ m n,JointSuspensions (canonicalStreaming R) retire initial p m n ∧
      residentAtlasBits (stackBank R.births initial p)+m+n+directoryBits (stackBank R.births initial p)≤
        absoluteSelectedRoof (s:=s) (C:=C) initial r.edges r.prec pageBound+
          descriptorBudget initial r.edges (pathLimit s C) fixed port body := by
  obtain ⟨m,n,trace,bound⟩ := actual_absolute_path_selected_peak R retire initial qFit pageBound rows bits p
  exact ⟨m,n,trace,Nat.add_le_add bound
    (bounded_descriptor_stack_at_original_start R.births initial fixed port body fields p)⟩

theorem same_path_header_copy_has_selected_peak
    (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack R.births initial)
    (qFit : q≤uniformWidth s C) (pageBound fixed port body U : ℕ)
    (rows : AllExactPages R.births) (fields : SourceHeaderFit R.births fixed port body)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (path : Path sel r x) (w : (Plan sel).Slot x),
      let e := (R.births path w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound)
    (rootFit : ∀ x∈initial.headers,x.bytes.length≤U)
    (p : Path sel r c) (w : (Plan sel).Slot c) :
    let live := stackBank R.births initial p
    let j := (R.births p w).job
    ∃ m n,JointSuspensions (canonicalStreaming R) retire initial (.step p w) m n ∧
      ∀ temp∈selectedInstallSnapshots j.entry live.headers,
        residentAtlasBits live+pendingPageBits j+m+n+directoryBits live+temp.length≤
          absoluteSelectedRoof (s:=s) (C:=C) initial r.edges r.prec pageBound+
            descriptorBudget initial r.edges (pathLimit s C) fixed port body+
              (2*key+3*max U (fixed+(3*r.edges/29)*(port+body))+1) := by
  let live := stackBank R.births initial p
  let j := (R.births p w).job
  let V := max U (fixed+(3*r.edges/29)*(port+body))
  obtain ⟨m,n,trace,bank⟩ := actual_absolute_path_selected_peak R retire initial qFit pageBound rows bits
    (.step p w)
  change residentAtlasBits (afterOne live j)+m+n≤_ at bank
  rw [true_queued_pages_are_exact_increment] at bank
  have dir := bounded_descriptor_stack_at_original_start R.births initial fixed port body fields p
  have outputFit : j.entry.result.bytes.length≤V :=
    (next_descriptor_fits_geometric_cap R.births fixed port body fields p w).trans (le_max_right _ _)
  have allFit := live_headers_fit_same_geometric_cap R.births initial fixed port body fields U rootFit p
  have fresh : ∀ row∈live.headers,row.id≠j.entry.result.id :=
    (legal p w).2.2 j List.mem_cons_self
  refine ⟨m,n,trace,fun temp mem=>?_⟩
  exact Nat.add_le_add (Nat.add_le_add bank dir)
    (actual_fresh_install_temporary_bits j.entry live.headers fresh allFit outputFit temp mem)

#print axioms true_queued_pages_are_exact_increment
#print axioms same_scoped_ancestry_with_resident_descriptors
#print axioms same_path_header_copy_has_selected_peak
end J6R51Peak
