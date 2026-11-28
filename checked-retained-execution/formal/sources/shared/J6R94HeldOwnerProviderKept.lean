import J6R94HeldOwnerProviderCap
import J6R94HeldOwnerProviderRetainRoster

/-! Attach the actual R59 kept raw owner result to the actual next R65 site of the same selected local load. The roster transport is erased and preserves every raw byte. -/
namespace J6R94HeldOwnerProvider
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
local notation "deg" => (4*Nat.clog 2 s)
local notation "ch" => (p.ticket w).child

open J6R51ParentFrames J6R52CacheWhole J6R52CacheSource J6R59Public J6R30ProducedGateRegistry

section Transfer
variable {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
variable {S D : StoredSite T v key prec tw bw (pageKeyWidth m+pad)}
variable {g : v.parent.host.Row⊕v.parent.host.Col→
  Option (CodeGate (Word (pageKeyWidth m+J6Mesh.a m)))}

def moveOwnerRoster (eq : S=D)
    (roster : CompleteRoster S.site.oldKey (parentData S g)) :
    CompleteRoster D.site.oldKey (parentData D g) := by
  rw [←eq]
  exact roster

theorem move_owner_roster_preserves_raw (eq : S=D)
    (roster : CompleteRoster S.site.oldKey (parentData S g)) :
    (moveOwnerRoster (X:=X) eq roster).order=roster.order ∧ HEq (moveOwnerRoster (X:=X) eq roster).raw roster.raw := by
  cases eq
  exact ⟨rfl,HEq.rfl⟩
end Transfer

local notation "prior" => (sourceState M p w)
local notation "priorGates" => (gateHistory T (bootGates X) p)
variable (u : (Plan sel).Slot (p.ticket w).child)
variable (K : Meter (HeldOwnerLoad (sourceState M p w) (u:=u) (gateHistory T (bootGates X) p)))
variable (cache : CachedParentFrames (sourceState M p w).site)
variable (keys : NativeCreationOwnerContext (sourceState M p w) K.result.load)
variable (picked : K.result.load=(M.demand (sourceState M p w) u).result)

include picked in
theorem prior_held_load_is_same_next_source :
    (cachedAdvance (prior) u K.result.load cache).next=sourceState M (.step p w) u := by
  simp only [cached_advance_exact,picked,sourceState]

def rosterActuallyCarriedToNext :
    CompleteRoster (sourceState M (.step p w) u).site.oldKey
      (parentData (sourceState M (.step p w) u) (gateHistory T (bootGates X) (.step p w))) :=
  moveOwnerRoster (X:=X) (prior_held_load_is_same_next_source X M p w u K cache picked)
    (carriedRosterForCachedChild (prior) (priorGates) K.result cache keys)

theorem actual_held_roster_is_same_raw_source_at_next_slot :
    let R := rosterActuallyCarriedToNext X M p w u K cache keys picked
    R.order=K.result.held.order ∧ HEq R.raw K.result.held.raw := by
  have move := move_owner_roster_preserves_raw (X:=X)
    (prior_held_load_is_same_next_source X M p w u K cache picked)
    (carriedRosterForCachedChild (prior) (priorGates) K.result cache keys)
  have kept := carried_roster_has_the_actual_raw_payload (prior) (priorGates) K.result cache keys
  exact ⟨move.1.trans kept.1,HEq.trans move.2 kept.2⟩

include picked in
theorem actual_R65_entry_uses_the_same_held_child_bank (initial : Bank) :
    stackBank (borns M) initial (.step (.step p w) u)=
      afterOne (stackBank (borns M) initial (.step p w))
        (cachedAdvance (prior) u K.result.load cache).next.birth.job := by
  rw [prior_held_load_is_same_next_source X M p w u K cache picked]; rfl

#print axioms actual_held_roster_is_same_raw_source_at_next_slot
#print axioms actual_R65_entry_uses_the_same_held_child_bank
end
end J6R94HeldOwnerProvider