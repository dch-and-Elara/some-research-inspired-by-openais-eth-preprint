import J6R110CanonicalCoverageMount

/-! The real chart builder and one installer have named local cuts:
an reached counter pause, a serialization prefix, or the source and
installed raw views. The ambient words can stay live across any cut. -/
namespace J6R110CanonicalAllPeak
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 J6ActiveRun J6R9Recursive
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R27PrescribedProbe J6R50RootIngress
open J6R109CanonicalProbeTable J6R110CanonicalCoverage J6R110CanonicalMount J6R75RawPeak

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 13500000

noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "e" => f.natDegree
local notation "d" => fullProbeDegree f.natDegree
local notation "n" => (fullProbeDegree f.natDegree+1)
local notation "fit" => full_probe_fit f.natDegree

def CanonicalBootCut (T : Prepared cfg sel r hf)
    (bytes : (canonicalTable e n).result=OldOrderedBytes e d fit) (bits : ℕ) : Prop :=
  (∃ (left : ℕ) (saved : List (Word e)) (cursor : Word e),
    0<left ∧ CounterPause (wordOne e) (encoded e 0) d saved cursor left ∧
    bits=selectedEmitPayload e left saved cursor) ∨
  (∃ (offset : ℕ) (pre : List (Word e)) (head : Word e) (post : List (Word e)),
    (indexTape e n).result=pre++head::post ∧
    bits=selectedCopyPayload (indexTape e n).result pre head post offset) ∨
  bits=gridMemoryBits (canonicalTable e n).result+gridMemoryBits (mountFullChart T bytes).result.table.raw

theorem actual_canonical_boot_cut_fits (T : Prepared cfg sel r hf)
    (bytes : (canonicalTable e n).result=OldOrderedBytes e d fit)
    (bits : ℕ) (cut : CanonicalBootCut T bytes bits) : bits≤264*s^5 := by
  obtain ⟨_,_,_,_,_,_,_,install,generation⟩ :=
    actual_full_mount_has_one_printed_polynomial_fee_and_selected_workspace T bytes
  have phase := actual_probe_table_has_a_single_selected_local_peak e d
  rcases cut with ⟨left,saved,cursor,working,reached,rfl⟩|rest
  · exact (phase.1 left saved cursor working reached).trans generation
  rcases rest with ⟨offset,pre,head,post,reached,rfl⟩|finish
  · exact (phase.2 offset pre head post reached).trans generation
  rw [finish]
  exact install.trans (Nat.mul_le_mul_right _ (by decide))

theorem same_entry_boot_and_regional_pause_take_maximum
    (T : Prepared cfg sel r hf)
    (bytes : (canonicalTable e n).result=OldOrderedBytes e d fit)
    (ambient built live regionalRoof : ℕ)
    (cut : CanonicalBootCut T bytes built) (bounded : live≤regionalRoof) :
    max (ambient+built) live≤max (ambient+264*s^5) regionalRoof :=
  max_le_max (Nat.add_le_add_left (actual_canonical_boot_cut_fits T bytes built cut) _) bounded

#print axioms actual_canonical_boot_cut_fits
#print axioms same_entry_boot_and_regional_pause_take_maximum
end
end J6R110CanonicalAllPeak
