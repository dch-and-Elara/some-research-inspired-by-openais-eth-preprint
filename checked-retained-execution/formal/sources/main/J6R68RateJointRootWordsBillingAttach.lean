import J6R68RateJointRootWordsBillingIngress
import J6R68RateJointRootWordsBillingAttachBody
import J6R55TerminalBootJoinedFee

/-! Concrete R55 instance of the first-ingress contract. Unlike the
general receipt it fixes the remaining charge to the same observed
owner mount, seat table, origin projection and addon emission. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R35RootOrigins
open J6R26DescriptorTree J6R33StatefulArithmeticPage J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R55BootBodies J6R30ProducedGateRegistry J6R55TerminalBootJoined
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R51Online J6R32StatefulArithmetic J6R48RawRoute
open J6R54ExteriorOwner J6R55TerminalOrigin J6R53OldOwnerRoot J6R50SourceProducer

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4500
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own rate : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Slot" => ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
variable (A : FirstBodyProgram X gate pad T)
variable (make : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group),
  Meter (FirstSlotBook (r:=exteriorChild G ell X.centre X.sample X.group) (sel:=sel) T key prec tw bw (pageKeyWidth m+pad) w))
variable (uses : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group),A.old w = loadSelectedFirst (T:=T) (w:=w) (make w) X.issue.result)

variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)
variable (D : OwnerWordsAtBodies X gate pad root A)
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (inj : Function.Injective rootName)

def joinedOwnerDebit (w : Slot) : ℕ :=
  let Y := joinedSlots X gate pad root A D w
  let mounted := mountFirstOwners X gate pad root B live (D.keys w) inj
  let add := J6R48GeneratedAddons.emit (readBootAddon Y.words mounted.result)
    (compileOccurrence Y.occurrence.result).native.physical.order
  mounted.steps+Y.words.seats.steps+(projectOriginTape mounted.result.raw).steps+add.steps

def ingressOfActualJoinedMachine :
    ActualFirstIngress (withJoinedBoot X gate pad root M A D B live inj) where
  exteriorKey := X.issue.result
  build := make
  port := fun _=>rootHalfWidth m+1
  writer := fun w=>readFirstPhysical X gate pad A.lanes (A.seats w)
  ownerDebit := joinedOwnerDebit X gate pad A root D B live inj
  actualInput := fun w=>(joined_source_identity X gate pad root M A D B live inj w).trans
    (congrArg Meter.result (real_joined_body_is_replacement X gate pad A make uses w))
  actualSteps := by
    intro w
    let Y := joinedSlots X gate pad root A D w
    let mounted := mountFirstOwners X gate pad root B live (D.keys w) inj
    let add := J6R48GeneratedAddons.emit (readBootAddon Y.words mounted.result)
      (compileOccurrence Y.occurrence.result).native.physical.order
    have q := (joined_initial_body_and_mount_charged_once X gate pad root M A D B live inj w).1
    have body := congrArg Meter.steps (real_joined_body_is_replacement X gate pad A make uses w)
    change (bodyAtActualSlot X gate pad A w).steps=_ at body
    change ((withJoinedBoot X gate pad root M A D B live inj).initial w).steps=
      (bodyAtActualSlot X gate pad A w).steps+mounted.steps+Y.words.seats.steps+
        (projectOriginTape mounted.result.raw).steps+add.steps at q
    change _=(replaceSelectedFirst (T:=T) (w:=w) (make w) X.issue.result
      (readFirstPhysical X gate pad A.lanes (A.seats w))).steps+
      (mounted.steps+Y.words.seats.steps+(projectOriginTape mounted.result.raw).steps+add.steps)
    rw [q,body]
    ac_rfl

#print axioms ingressOfActualJoinedMachine
end
end J6R68RateJoint.RootWords

