import J6R68RecursivePeakScope
import J6R57LiveSpaceCachedStack

/-! While the parent arithmetic is suspended, compare actual prefixes
of the outgoing child tape and addon writer to the true enlarged live
state. This is a monotone reserve across named phases, not a replacement
for unobserved supplier or Page compiler temporaries. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R52Peak J6R52CacheWhole J6R53PeakAddon J6R54PeakInput
open J6R57LiveSpace J6R66.BootPeak
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4060
set_option maxHeartbeats 13300000
set_option Elab.async false

inductive ChildWritePoint where
  | emitting (ports raw : ℕ)
  | indexing (ports index : ℕ)

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)

def recursiveStagingBits
    (M : OnlineMachine T key prec tw bw page q) (B : PageBank f ell key prec tw bw page)
    (p : Path sel r c) (w : (@Plan f ell s sel).Slot c)
    (shared pausedAncestor : ℕ) (point : ChildWritePoint) : ℕ :=
  let X := sourceState M p w
  let parent := stackBank (borns M) B p
  let next := X.birth.job
  let addedPort := fun n : ℕ => ((sourcePhysicalBitTape X.input).take n).length
  let base := shared+pausedAncestor+(mountedSelectedBits parent+mountedInsertionBits next)+
    physicalInputStackBits M p
  match point with
  | .emitting n k => base+addedPort n+selectedAncestralIngress M p+emittedPrefixBits M p w k
  | .indexing n k => base+addedPort n+selectedAncestralIngress M p+
      (storedRawBits X).length+installedPrefixBits M p w k

def recursiveEnteredBits
    (M : OnlineMachine T key prec tw bw page q) (B : PageBank f ell key prec tw bw page)
    (p : Path sel r c) (w : (@Plan f ell s sel).Slot c)
    (shared pausedAncestor : ℕ) : ℕ :=
  shared+pausedAncestor+mountedSelectedBits (stackBank (borns M) B (.step p w))+
    cachedIngressBits M (.step p w)

theorem suspended_parent_plus_staging_fits_the_actual_child_reserve
    (M : OnlineMachine T key prec tw bw page q) (B : PageBank f ell key prec tw bw page)
    (p : Path sel r c) (w : (@Plan f ell s sel).Slot c)
    (shared pausedAncestor : ℕ) (point : ChildWritePoint) :
    recursiveStagingBits M B p w shared pausedAncestor point≤
      recursiveEnteredBits M B p w shared pausedAncestor := by
  let X := sourceState M p w
  let parent := stackBank (borns M) B p
  have exact := publication_adds_exact_selected_record parent X.birth.job
  have bank :
      mountedSelectedBits (stackBank (borns M) B (.step p w))=
        mountedSelectedBits parent+mountedInsertionBits X.birth.job := exact
  have pair := fun (k : ℕ) => phase_does_not_double_count_the_stored_raw_input M p w k
  have ports (n : ℕ) :
      ((sourcePhysicalBitTape X.input).take n).length≤(sourcePhysicalBitTape X.input).length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  have ingress : cachedIngressBits M (.step p w)=
      physicalInputStackBits M p+(sourcePhysicalBitTape X.input).length+
        selectedAncestralIngress M (.step p w) := rfl
  unfold recursiveEnteredBits
  rw [bank,ingress]
  let fixedPart := shared+pausedAncestor+(mountedSelectedBits parent+mountedInsertionBits X.birth.job)+
    physicalInputStackBits M p
  cases point with
  | emitting n k =>
    unfold recursiveStagingBits
    dsimp only
    have h := Nat.add_le_add (Nat.add_le_add_left (ports n) fixedPart) (pair k).1
    simpa only [fixedPart,Nat.add_assoc] using h
  | indexing n k =>
    unfold recursiveStagingBits
    dsimp only
    have h := Nat.add_le_add (Nat.add_le_add_left (ports n) fixedPart) (pair k).2
    simpa only [fixedPart,Nat.add_assoc] using h

#print axioms recursiveStagingBits
#print axioms suspended_parent_plus_staging_fits_the_actual_child_reserve
end
end J6R68.RecursivePeak
