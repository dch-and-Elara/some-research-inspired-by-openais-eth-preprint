import J6R54PeakInputOccurrence
import J6R54PeakInputPath

/-! Four separately named logical payloads on the same path. The
physical parent-port tape comes from StoredSite.input, not from
a supplied bound on a replacement catalogue. The reserve is
conservative if any of these logical observers share storage. -/
namespace J6R54PeakInput
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R16ModeCost J6R36ChildFramedRoute J6R41StructuredAllPaths J6R50SourceProducer
open J6R51Peak J6R51Online J6R51ParentFrames J6R52Peak J6R52CacheWhole J6R53PeakAddon

set_option autoImplicit false
set_option maxRecDepth 3650
set_option maxHeartbeats 17800000
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

def physicalInputStackBits (M : OnlineMachine T key prec tw bw page q) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ
  | _, .root => 0
  | _, .step p w => physicalInputStackBits M p+(sourcePhysicalBitTape (sourceState M p w).input).length

theorem actual_physical_port_path_payload_cap
    (M : OnlineMachine T key prec tw bw page q) (fixed addr seed : ℕ)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed) (p : Path sel r c) :
    physicalInputStackBits M p≤2*((32*r.edges/29)-c.edges)*(addr+sourceBodyCap s C seed) := by
  let U := addr+sourceBodyCap s C seed
  have reserve : physicalInputStackBits M p≤2*parentEdgesOnPath p*U := by
    induction p with
    | root => simp [physicalInputStackBits,parentEdgesOnPath]
    | step p w ih =>
      simp only [physicalInputStackBits,parentEdgesOnPath,Nat.mul_add,Nat.add_mul]
      exact Nat.add_le_add ih (actual_demanded_occurrence_port_bits_uniform M fixed addr seed sizes boot p w)
  exact reserve.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (parent_edge_sum_uniform p)))

theorem measured_fields_of_both_source_records_and_caches
    (M : OnlineMachine T key prec tw bw page q) (fixed addr seed owner : ℕ)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (owners : OwnerWidth M owner) (p : Path sel r c) :
    physicalInputStackBits M p+(rawStackBits M p+addonStackBits M p+cacheStackBits M p)≤
      2*((32*r.edges/29)-c.edges)*(addr+sourceBodyCap s C seed+rawAndIndexedRowCap s addr owner key prec page)+
        (3*r.edges/29)*cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed) := by
  have h := Nat.add_le_add
    (actual_physical_port_path_payload_cap M fixed addr seed sizes boot p)
    (actual_raw_indexed_and_frame_reserves_same_stack M fixed addr seed owner sizes boot owners p)
  simpa only [Nat.mul_add,Nat.add_assoc] using h

#print axioms actual_physical_port_path_payload_cap
#print axioms measured_fields_of_both_source_records_and_caches
end
end J6R54PeakInput
