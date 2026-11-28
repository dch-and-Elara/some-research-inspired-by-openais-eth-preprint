import J6R53PeakAddonVisits
import J6R52CacheWholeRoot

/-! On a legal path of the same source, the mounted frames and the
actual installed addon banks have separate caps. This is a selected
space reserve, not a claim that the runtime allocator implements the
specified reuse or that other state is free. -/
namespace J6R53PeakAddon
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R16ModeCost J6R36ChildFramedRoute J6R41StructuredAllPaths J6R50SourceProducer
open J6R51Peak J6R51Online J6R51ParentFrames J6R52Peak J6R52CacheWhole

set_option autoImplicit false
set_option maxRecDepth 3650
set_option maxHeartbeats 18500000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

theorem same_cache_aware_source_value_and_selected_addon_reserve
    [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    (legal : ReadyOnStack (borns M) initial) (leaves : LeafAgreement M initial)
    (fixed addr seed owner : ℕ) (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (owners : OwnerWidth M owner) :
    let out := runCachedRoot M retire initial
    (T.frame (Path.root : Path sel r r).reached).decode out.result.1=
       (sourceBlueprint sel r hf).program.run r ∧ out.result.2=initial ∧
    ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c),
      ObservedBankPath M retire initial p (addonStackBits M p) ∧
      addonStackBits M p+cacheStackBits M p≤
        2*((32*r.edges/29)-c.edges)*commonAddonRowCap s addr owner key prec page+
          (3*r.edges/29)*cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed) := by
  obtain ⟨v,back⟩ := fully_cached_selected_source M initial retire legal leaves
  exact ⟨v,back,fun p=>⟨true_cache_aware_entries_realize_the_addon_observation M retire initial legal p,
    actual_separate_addon_and_frame_fields_share_the_same_path M fixed addr seed owner sizes boot owners p⟩⟩

#print axioms same_cache_aware_source_value_and_selected_addon_reserve
end J6R53PeakAddon
