import J6R55BootBodiesLanes
import J6R53TerminalGateWhole
import J6R62LeafCensus
import J6R54ExteriorOwnerMount
import J6R67CanonicalStopRoot

/-! An executable root input join on the already emitted R37 lanes.
The owner words are independently purchased in the very same exterior
edge order, as witnessed by the native endpoint map. We do not infer
them from an untyped list, synthesize a fresh seed, or pay for a
second installation. Borrowed lane bodies remain under their original
allocation; only the owner word and outer list records are copied. -/
namespace J6R67CanonicalStop
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R55BootBodies J6R48RawRoute J6R50SourceProducer J6R54ExteriorOwner
open J6R53OldOwner J6R62Leaf J6R50Leaf J6R52Terminal J6R53TerminalGate

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4200
set_option Elab.async false

section Raw
variable {m key prec pad own : ℕ}
local notation "Pair" => (RootLanes m key prec pad)
local notation "Fr" => (FramedEdge (rootHalfWidth m) own key prec (pageKeyWidth m+pad))

def laneFrame (who : Word own) (L : Pair) : Fr := ⟨who,L.gate,L.packet⟩

def assembleRootFrames : List (Word own) → List Pair → Meter (Option (List Fr))
  | [],[] => ⟨some [],3⟩
  | x::xs,l::ls =>
    let w := copyFixed x
    let rest := assembleRootFrames xs ls
    ⟨rest.result.map (fun fs=>laneFrame w.result l::fs),w.steps+rest.steps+7⟩
  | _,_ => ⟨none,4⟩

theorem paid_exact_root_frame_join {E : Type} (who : E→Word own) (ports : E→Pair)
    (edges : List E) :
    assembleRootFrames (edges.map who) (edges.map ports)=
      ⟨some (edges.map (fun x=>laneFrame (who x) (ports x))),3+edges.length*(3*own+8)⟩ := by
  induction edges with
  | nil => simp only [List.map_nil,assembleRootFrames,List.length_nil,Nat.zero_mul,Nat.add_zero]
  | cons x xs ih =>
    simp only [List.map_cons,assembleRootFrames,ih,copy_fixed_exact,Option.map_some,
      List.length_cons,Nat.succ_mul]
    congr 1
    omega
end Raw

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Fr" => (FramedEdge (rootHalfWidth m) own key prec (pageKeyWidth m+pad))
local notation "Owners" => ((exteriorChild G ell X.centre X.sample X.group).host.Row⊕
  (exteriorChild G ell X.centre X.sample X.group).host.Col)

def exteriorOldOwnerWord (name : Owners→Word own)
    (e : (exteriorChild G ell X.centre X.sample X.group).host.Edge) : Word own :=
  name (.inl ((exteriorChild G ell X.centre X.sample X.group).host.network.row e))

def exteriorFrameAt (name : Owners→Word own)
    (e : (exteriorChild G ell X.centre X.sample X.group).host.Edge) :
    FramedEdge (rootHalfWidth m) own key prec (pageKeyWidth m+pad) :=
  laneFrame (exteriorOldOwnerWord X name e) (laneView X gate pad e)

structure PaidIncidentNames (name : Owners→Word own) where
  emitted : Meter (List (Word own))
  same : emitted.result=(orderedExteriorEdges X).map (exteriorOldOwnerWord X name)

def assembleTrueExteriorFrames (name : Owners→Word own)
    (owners : PaidIncidentNames X name) (lanes : BootLaneTape X gate pad) :
    Meter (Option (List (FramedEdge (rootHalfWidth m) own key prec (pageKeyWidth m+pad)))) := by
  let run := @assembleRootFrames m key prec pad own owners.emitted.result lanes.run.result
  exact ⟨run.result,owners.emitted.steps+lanes.run.steps+run.steps+4⟩

theorem paid_mounted_root_frames_exact (name : Owners→Word own)
    (owners : PaidIncidentNames X name) (lanes : BootLaneTape X gate pad) :
    assembleTrueExteriorFrames X gate pad name owners lanes=
      ⟨some ((orderedExteriorEdges X).map (exteriorFrameAt X gate pad name)),
        owners.emitted.steps+lanes.run.steps+
          (orderedExteriorEdges X).length*(3*own+8)+7⟩ := by
  unfold assembleTrueExteriorFrames
  dsimp only
  rw [owners.same,lanes.exact,paid_exact_root_frame_join]
  dsimp only
  congr 1
  omega

theorem true_root_frame_roster_census (name : Owners→Word own) :
    ((orderedExteriorEdges X).map (exteriorFrameAt X gate pad name)).length=
      Nat.card ((exteriorChild G ell X.centre X.sample X.group).host.Edge) :=
  (List.length_map _).trans
    (actual_complete_order_length _ (reviewed_exterior_order X).1 (reviewed_exterior_order X).2)


#print axioms assembleRootFrames
#print axioms paid_exact_root_frame_join
#print axioms paid_mounted_root_frames_exact
#print axioms true_root_frame_roster_census
end
end J6R67CanonicalStop

