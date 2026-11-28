import J6R53PeakAddonPath
import J6R52PeakCachedPhase

/-! Factor the existing active branch through the paid mount. The
explicit ResidentBank is consumed by that mount and is not an argument
to the later phase. The StoredSite and callbacks remain, however:
nothing here requires that all runtime references are released, or
that a callback cannot compute another representation from the site. -/
namespace J6R53PeakAddon
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R16ModeCost J6R36ChildFramedRoute J6R41StructuredAllPaths J6R48RawRoute J6R50SourceProducer
open J6R51Peak J6R51Online J6R51ParentFrames J6R52Peak J6R52CacheWhole

set_option autoImplicit false
set_option maxRecDepth 3750
set_option maxHeartbeats 19000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def afterPaidMount
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (a : (S).cutoff<((P).child c u).edges)
    (mounted : Meter (CachedParentFrames X.site)) (B : L) :
    Meter (Block (T.frame (Path.step p u).reached) ell × L) :=
  let here := Path.step p u
  let d := ready_reachable cfg sel here.reached T.rootStable a
  let A := M.activeAfter p u X a
  let out := A.result.eval M.modeWidth (reachable_positive T here.reached) T.vPositive hf
    (fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openBankDemand (M.demand X w) mounted.result retire
        (fun next bank=>runCachedAfter M retire ((P).child c u) here w next bank)
        (zeroM (T.bank (registerPrecision S ((P).child c u) t) (register_positive d t)).hp) B))
  ⟨(out.result,B),mounted.steps+A.steps+out.steps⟩

theorem actual_active_branch_factors_through_its_paid_mount
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (a : (S).cutoff<((P).child c u).edges)
    (bank : ResidentBank X) (B : L) :
    runCachedAfter M retire c p u X bank B=afterPaidMount M retire p u X a (mountResident X bank) B := by
  rw [runCachedAfter,dif_neg (Nat.not_le.mpr a)]
  rfl

theorem cached_stop_skips_the_mount_of_the_supplied_bank
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (stop : ((P).child c u).edges≤(S).cutoff)
    (bank : ResidentBank X) (B : L) :
    let leaf := M.leafAfter p u X stop B
    runCachedAfter M retire c p u X bank B=⟨(leaf.result,B),leaf.steps⟩ := by
  dsimp only
  rw [runCachedAfter,dif_pos stop]

theorem actually_installed_bank_and_mounted_frames_have_disjoint_encoding_caps
    (M : OnlineMachine T key prec tw bw page q) (fixed addr seed owner : ℕ)
    (sizes : EntryWidths M fixed addr) (owners : OwnerWidth M owner) (boot : BootBodyWidth M seed)
    (p : Path sel r c) (w : (P).Slot c) (a : (S).cutoff<((P).child c w).edges) :
    let incoming := sourceBankAt M p w
    let mounted := sourceMounted (M:=M) p w
    (residentAddonPayload incoming.result).length+(cachedWireBits mounted.result).length≤
      (2*c.edges)*commonAddonRowCap s addr owner key prec page+
        ((P).child c w).edges*
          cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed) := by
  have h := source_selected_cache_row_width M fixed addr seed owner sizes boot owners p w
  rw [actualMountedFields,if_pos a] at h
  exact Nat.add_le_add (exact_site_parent_rows_have_uniform_width M fixed addr owner sizes owners p w) h

#print axioms actual_active_branch_factors_through_its_paid_mount
#print axioms cached_stop_skips_the_mount_of_the_supplied_bank
#print axioms actually_installed_bank_and_mounted_frames_have_disjoint_encoding_caps
end
end J6R53PeakAddon
