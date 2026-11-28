import J6R55TerminalOriginPath
import J6R55BootBodiesMachine

/-! One actual first slot: build the original exterior physical bodies
and use the measured live owner mount for the same occurrence. The
boot receipt for this very online machine has no supplied origin or
physical-body equation. Its issued word and its issued fee both survive. -/
namespace J6R55TerminalBootJoined
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R41StructuredAllPaths J6R51Online J6R55TerminalOrigin J6R54TerminalBoot J6R55BootBodies
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 6100
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own rate : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)



variable (M : (OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate))

variable (A : FirstBodyProgram X gate pad T)

structure OwnerWordsAtBodies (A : FirstBodyProgram X gate pad T) where
  width : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))→ℕ
  name : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group), (exteriorChild G ell X.centre X.sample X.group).host.Row⊕(exteriorChild G ell X.centre X.sample X.group).host.Col→Word (width w)
  distinct : ∀ w, Function.Injective (name w)
  keys : ∀ w, KeyInputs X gate pad root (name w)
  ports : ∀ w, BootPortWords (bodyAtActualSlot X gate pad A w).result (name w)

variable (D : OwnerWordsAtBodies X gate pad root A)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)

def joinedSlots (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) : LiteralFirstSlot X gate pad root w T :=
  ⟨bodyAtActualSlot X gate pad A w,D.width w,D.name w,D.distinct w,D.keys w,D.ports w⟩

def withJoinedBoot : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate :=
  withGeneratedOrigins X gate pad root M (joinedSlots X gate pad root A D) B live rootInj

theorem actual_joined_boot_is_literal :
    ExactPrintedBoot X (withJoinedBoot X gate pad root M A D B live rootInj) gate :=
  origin_seam_retains_only_body_receipt X gate pad root M (joinedSlots X gate pad root A D)
    B live rootInj (every_produced_first_slot_has_original_body X gate pad A)

theorem joined_source_identity (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) :
    ((withJoinedBoot X gate pad root M A D B live rootInj).initial w).result.input=(bodyAtActualSlot X gate pad A w).result := rfl

theorem joined_issued_meter_is_original (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) :
    ((withJoinedBoot X gate pad root M A D B live rootInj).initial w).result.input.issued=(A.old w).result.issued := by
  change (bodyAtActualSlot X gate pad A w).result.issued=(A.old w).result.issued
  exact (replaced_boot_keeps_real_numeric_and_atlas_words X gate pad w (A.old w) A.lanes (A.seats w)).2.1

end
#print axioms joinedSlots
#print axioms withJoinedBoot
#print axioms actual_joined_boot_is_literal
#print axioms joined_source_identity
#print axioms joined_issued_meter_is_original
end J6R55TerminalBootJoined
