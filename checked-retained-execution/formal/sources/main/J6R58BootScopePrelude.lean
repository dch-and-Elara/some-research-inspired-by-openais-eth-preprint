import J6R58BootScopeWriter
import J6R55BootBodiesLanes

/-! The original first writer copies the already available two-lane
order once per true exterior edge. The true tagged reader scans the
two named lists and expressly pays its finite per-port address query. -/
namespace J6R58BootScope
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R48GeneratedAddons J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R53OldOwner J6R54ExteriorOwner J6R41StructuredAllPaths J6R51Online
open J6R55TerminalOrigin J6R55BootBodies J6R57ScopeFee J6R16ModeCost J6R51Peak
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 5900
set_option Elab.async false
noncomputable section


variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)

def actualLanePreludeCeiling (m ro co de pad key prec selected : ℕ) : ℕ :=
  halfTapeFee m ro co de+3+
    (2*J6Mesh.M m)*(2*rootHalfWidth m+3*(pageKeyWidth m+a m)+81)+
    (J6R37StructuredRoot.laneFee m pad key prec+6)*selected+4

theorem paid_original_boot_lane_prelude_has_source_geometry :
    let L := freshBootLaneTape X gate pad
    L.run.result=(outerLanes X gate pad).result.lanes ∧
      L.run.steps≤actualLanePreludeCeiling m ro co de pad key prec (orderedExteriorEdges X).length := by
  let F := freshBootLaneTape X gate pad
  let half := makeHalfTape m [] X.source.raw
  let i : Fin (a m) := ⟨0,Nat.zero_lt_of_lt (oddAxis m).isLt⟩
  have halfExact := actual_root_half_tape X.source i [] (by rfl)
  have halfValue : half.result=(rootHalfOrder m).map (expectedHalfRow P i) := halfExact.1
  have halfLen : half.result.length=2*J6Mesh.M m := halfExact.2.1
  have halfFee : half.steps≤halfTapeFee m ro co de := halfExact.2.2
  have scan : (half.result.map rowScanFee).sum≤
      (2*J6Mesh.M m)*(2*rootHalfWidth m+3*(pageKeyWidth m+a m)+81) := by
    rw [←halfLen]
    apply uniform_sum_bound
    intro x hx
    rw [halfValue] at hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    change 2*rootHalfWidth m+3*((physicalSeatField (rootChart P) i
      (residentPageKey m) (edge y)).page.bits++(physicalSeatField (rootChart P) i
      (residentPageKey m) (edge y)).slot.bits).length+81≤_
    rw [List.length_append,Word.size,Word.size]
  have charged := actual_fresh_lane_file_and_fee X gate pad
  refine ⟨charged.1,?_⟩
  have c : F.run.steps = half.steps+3+(half.result.map rowScanFee).sum+
      (J6R37StructuredRoot.laneFee m pad key prec+6)*(orderedExteriorEdges X).length+4 := charged.2
  change F.run.steps≤_
  rw [c]
  unfold actualLanePreludeCeiling
  omega

def withSharedBootLanePrelude {Y : Type*} (next : BootLaneTape X gate pad→Meter Y) : Meter Y :=
  let lanes := freshBootLaneTape X gate pad
  let one := next lanes
  ⟨one.result,lanes.run.steps+one.steps⟩

theorem shared_boot_prelude_charged_once {Y : Type*} (next : BootLaneTape X gate pad→Meter Y) :
    (withSharedBootLanePrelude X gate pad next).result=(next (freshBootLaneTape X gate pad)).result ∧
      (withSharedBootLanePrelude X gate pad next).steps≤
        actualLanePreludeCeiling m ro co de pad key prec (orderedExteriorEdges X).length+
          (next (freshBootLaneTape X gate pad)).steps :=
  ⟨rfl,Nat.add_le_add_right (paid_original_boot_lane_prelude_has_source_geometry X gate pad).2 _⟩

end
#print axioms paid_original_boot_lane_prelude_has_source_geometry
#print axioms shared_boot_prelude_charged_once
end J6R58BootScope
