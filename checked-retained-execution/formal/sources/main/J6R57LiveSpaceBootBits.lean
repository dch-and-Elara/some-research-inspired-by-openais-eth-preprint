import J6R55SelectedPeakBootWriter
import J6R55BootBodiesLanes

/-! Exact selected bit width of the shared two-lane input itself.
The old Gate lane has no Page key in its origin; the other lane has
the current widened Page key. Its fixed label is not estimated from
the raw body size. This is one boot file, not one copy per DFS frame. -/
namespace J6R57LiveSpace
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R48RawRoute J6R11Blueprint J1PPrinted J6R24MeteredRecursion
open J6R51Peak J6R52Peak J6R55SelectedPeak J6R55BootBodies

set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3650
set_option maxHeartbeats 23000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

def rootLaneRowBits (m key prec pad : ℕ) : ℕ :=
  2*rootHalfWidth m+2*key+2*prec+2*pageKeyWidth m+2*a m+pad+7

theorem named_lane_bits_exact {w key prec pg : ℕ} (x : Lane w key prec pg) :
    (laneBits x).length=w+key+prec+2+(if x.origin.pageKey.isSome then pg else 0)+x.body.length := by
  simp only [laneBits,List.length_append,x.id.edge.size,List.length_cons,List.length_nil,origin_words_exact]
  omega

theorem root_lane_pair_has_exact_wire_and_creation_width (m pad : ℕ) {key prec : ℕ}
    (gate born : Stamp key prec) (b : Bool) (F : SeatField (a m) (pageKeyWidth m)) :
    (rootLanePairBits (rootLaneSpec m pad gate born b F)).length=rootLaneRowBits m key prec pad := by
  let x := rootLaneSpec m pad gate born b F
  have g0 : x.gate.origin.pageKey.isSome=false := rfl
  have p1 : x.packet.origin.pageKey.isSome=true := rfl
  have gb : x.gate.body.length=1+(pageKeyWidth m+a m) := by
    change (false::(F.page.bits++F.slot.bits)).length=_
    simp only [List.length_cons,List.length_append,F.page.size,F.slot.size,Nat.add_comm]
  have pb : x.packet.body.length=2+a m := by
    change (true::b::F.slot.bits).length=_
    simp only [List.length_cons,F.slot.size]
    omega
  change (laneBits x.gate++laneBits x.packet).length=_
  rw [List.length_append,named_lane_bits_exact,named_lane_bits_exact,g0,p1,gb,pb,rootLaneRowBits]
  simp only [Bool.false_eq_true,if_false,if_true,Nat.add_zero]
  omega

theorem constant_encoded_roster_width {A : Type*} (rows : List A) (enc : A→List Bool) (w : ℕ)
    (width : ∀ x∈rows,(enc x).length=w) :
    (rows.flatMap enc).length=rows.length*w := by
  induction rows with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul,
       width x List.mem_cons_self,ih (fun y hy=>width y (List.mem_cons_of_mem _ hy))]
    exact Nat.add_comm _ _

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {gate : Stamp key prec} {pad : ℕ}

theorem actual_exterior_lane_cell_width
    (h : (exteriorChild G ell X.centre X.sample X.group).host.Edge) :
    (rootLanePairBits (laneView X gate pad h)).length=rootLaneRowBits m key prec pad := by
  unfold laneView actualLane
  exact root_lane_pair_has_exact_wire_and_creation_width m pad _ _ _ _

def sharedBootBits (L : BootLaneTape X gate pad) : ℕ :=
  (L.run.result.flatMap rootLanePairBits).length

theorem exact_shared_boot_file_width (L : BootLaneTape X gate pad) :
    sharedBootBits X L=(orderedExteriorEdges X).length*rootLaneRowBits m key prec pad := by
  unfold sharedBootBits
  rw [L.exact, List.flatMap_map]
  exact constant_encoded_roster_width _ _ _ (fun x _=>actual_exterior_lane_cell_width X x)

#print axioms named_lane_bits_exact
#print axioms root_lane_pair_has_exact_wire_and_creation_width
#print axioms exact_shared_boot_file_width
end
end J6R57LiveSpace
