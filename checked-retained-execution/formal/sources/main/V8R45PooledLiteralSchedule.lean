import V8PooledMenuThreshold
import J6R12BlueprintReach

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
set_option maxRecDepth 2400

/-! No five-copy parameter is identified by a scaling argument: the
displayed manuscript sizes are the actual depth-zero printed schedule. -/
namespace V8R45PooledLiteral
open scoped Polynomial
open Polynomial V8PooledMenu V8PooledMenu.FiveCopy
open J6ActiveSchedule J1PPrinted J6R12Blueprint

variable (V : Type) [Fintype V]

theorem printed_root_width :
    stepU (Nat.clog 2 (rootSize V)) 0 = rootU V := by
  unfold stepU V8PooledMenu.FiveCopy.rootU epsDen
  rw [pow_zero,mul_one]

theorem printed_root_bits :
    stepA (Nat.clog 2 (rootSize V)) 0 = rootA V := by
  simp only [stepA,zero_add,Finset.range_one,Finset.sum_singleton,printed_root_width,rootA]

theorem printed_root_edges_linear :
    wireSize V ≤ 3*rootSize V := by unfold wireSize rootSize; omega

theorem printed_root_positive_edges : 0<wireSize V := by unfold wireSize; omega

theorem printed_root_slot_count :
    probeCount V = wireSize V * (2*2^rootA V-1)+1 := rfl

theorem printed_site_precision (t : Site V) :
    high t = childPrecision (rootPrec V) (stepA (Nat.clog 2 (rootSize V)) 0)
      (wireSize V) (stepU (Nat.clog 2 (rootSize V)) 0) t.val := by
  rw [printed_root_bits,printed_root_width]; rfl

theorem printed_site_increases (t : Site V) :
    rootPrec V < high t :=
  child_monotone _ _ _ _ t.val (printed_root_positive_edges V)

theorem printed_root_packet_guards (hu : 0<rootU V) :
    2*(J9PrintedSchedule.arrayCard (rootA V))^2*sourceDelta (rootSize V) ≤ wireSize V ∧
    2^rootA V*J9PrintedSchedule.arrayCard (rootA V) ≤ wireSize V ∧
    2*2^rootA V ≤ sourceDelta (rootSize V) := by
  have h := source_packing_conditions (rootSize V) (wireSize V) 0
    (show 1≤J9PrintedSchedule.rootU (Nat.clog 2 (rootSize V)) from hu)
    (root_leaf_guard V)
  change 2*(J9PrintedSchedule.arrayCard (stepA (Nat.clog 2 (rootSize V)) 0))^2*
      sourceDelta (rootSize V) ≤ wireSize V ∧
    2^(stepA (Nat.clog 2 (rootSize V)) 0)*
      J9PrintedSchedule.arrayCard (stepA (Nat.clog 2 (rootSize V)) 0) ≤ wireSize V ∧
    2*2^(stepA (Nat.clog 2 (rootSize V)) 0) ≤ sourceDelta (rootSize V) at h
  rwa [printed_root_bits] at h

variable {f : ℤ[X]}

theorem printed_root_coefficient_count (cfg : RootBounds (rootSize V) 3 f) :
    probeCount V ≤ 2^f.natDegree := by
  have h := fit_of_size (rootSize V) (wireSize V) 0 3 cfg.constSmall
    (printed_root_positive_edges V) (printed_root_edges_linear V) cfg.widthPos
  rw [←cfg.coefficient] at h
  change J9PrintedSchedule.probeCount (wireSize V)
    (2^stepA (Nat.clog 2 (rootSize V)) 0) ≤ 2^f.natDegree at h
  rw [printed_root_bits] at h
  exact h

theorem printed_root_coefficient_positive (cfg : RootBounds (rootSize V) 3 f) :
    0<f.natDegree := by
  have hs : 2≤rootSize V := by unfold rootSize; omega
  rw [cfg.coefficient]
  exact Nat.mul_pos (by decide) (Nat.clog_pos (by decide) hs)

#print axioms printed_root_width
#print axioms printed_root_bits
#print axioms printed_root_edges_linear
#print axioms printed_root_positive_edges
#print axioms printed_root_slot_count
#print axioms printed_site_precision
#print axioms printed_site_increases
#print axioms printed_root_packet_guards
#print axioms printed_root_coefficient_count
#print axioms printed_root_coefficient_positive
end V8R45PooledLiteral