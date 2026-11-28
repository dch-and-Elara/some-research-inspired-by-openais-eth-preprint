import J6R55PublicDirect
import J6R55TerminalBootJoinedCore
import J6R55PublicFamily

/-! Connect the two separately measured start producers to the very
same public dispatcher: the root body writer and first owner loader
fill the slots; successor lookup uses parent increment. No old live
boot, ReadyOnStack, tag equation or raw-body equation is supplied. -/
namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R14ZeroMode
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R15ModeCost J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R31RootResidentTables J6R50SourceProducer
open J6R51 J6R51Online J6R48DFS J6R54PublicFamily J6R16ModeCost
open J6R12Blueprint J6R10Reachable J6R11Blueprint J6ActiveRun J1PPrinted J6R26DescriptorTree
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R35RootOrigins J6R54ExteriorOwner
open J6R55TerminalBootJoined J6R55BootBodies J6R54TerminalBoot
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 29000000
set_option maxRecDepth 4800
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {A : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) A (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew rate own : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable (pad : ℕ)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W C i j g).hf}
variable (ops : OnlineOperators T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
variable (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad)
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable {name : SourceVertex A→Word own}
variable (root : RootRoster (P:=A) gate pad name)
variable (writer : FirstBodyProgram (literalSite W C i j g) gate pad T)
variable (owners : OwnerWordsAtBodies (literalSite W C i j g) gate pad root writer)
variable (rootInj : Function.Injective name)
variable (req : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
  (Y : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
  (u : (Plan (G.selector ell)).Slot v.child), Meter (FixedRequest Y u))

def joinedActualPublicMachine
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val) :
    OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate :=
  actualPublicMachine W C i j g pad ops B gate root
    (joinedSlots (literalSite W C i j g) gate pad root writer owners) rootInj req sync old

theorem measured_raw_boot_and_dispatch_share_the_same_ready_machine
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val)
    (capacity : nativeDepthCapacity W C i j g)
    (emits : ∀ w, (writer.old w).result.issued=issuedAtFirstDepth W C i j g) :
    let M := joinedActualPublicMachine W C i j g pad ops B gate root writer owners rootInj req sync old
    ExactPrintedBoot (literalSite W C i j g) M gate ∧
      ReadyOnStack (borns M) (actualInstalledBank W C i j g pad B) := by
  let X := literalSite W C i j g
  let bank := actualInstalledBank W C i j g pad B
  let live := (real_public_install_and_reserve W C i j g pad B sync old).2.1
  let M := joinedActualPublicMachine W C i j g pad ops B gate root writer owners rootInj req sync old
  let slots := joinedSlots X gate pad root writer owners
  have boot : withJoinedBoot X gate pad root M writer owners bank live rootInj=M := rfl
  have literal := actual_joined_boot_is_literal X gate pad root M writer owners bank live rootInj
  rw [boot] at literal
  refine ⟨literal,?_⟩
  intro c p u
  exact actual_machine_has_no_ready_input W C i j g pad ops B gate root slots rootInj req sync old capacity
    (fun w=>
      ((replaced_boot_keeps_real_numeric_and_atlas_words X gate pad w (writer.old w) writer.lanes
        (writer.seats w)).2.1).trans (emits w)) p u

#print axioms joinedActualPublicMachine
#print axioms measured_raw_boot_and_dispatch_share_the_same_ready_machine
end
end J6R55Public



namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R14ZeroMode
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R15ModeCost J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R31RootResidentTables J6R50SourceProducer
open J6R51 J6R51Online J6R48DFS J6R54PublicFamily J6R16ModeCost
open J6R12Blueprint J6R10Reachable J6R11Blueprint J6ActiveRun J1PPrinted J6R26DescriptorTree
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R35RootOrigins J6R54ExteriorOwner
open J6R55TerminalBootJoined J6R55BootBodies J6R54TerminalBoot
open J6R49SourceLayout
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 29000000
set_option maxRecDepth 4800
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {A : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) A (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew rate own : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable (pad : ℕ)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W C i j g).hf}
variable (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad)
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable {name : SourceVertex A→Word own}
variable (root : RootRoster (P:=A) gate pad name)
variable (writer : FirstBodyProgram (literalSite W C i j g) gate pad T)
variable (owners : OwnerWordsAtBodies (literalSite W C i j g) gate pad root writer)
variable (rootInj : Function.Injective name)
/-- Stamp the actual first record before executing the raw body/owner
producers.  This updates only the issue meter; the former issue word is
not consumed by either of those raw input producers. -/
def publicIssuedBodyProgram :
    FirstBodyProgram (literalSite W C i j g) gate pad T :=
  { writer with old := fun w =>
    let prev := writer.old w
    ⟨{prev.result with issued := issuedAtFirstDepth W C i j g},prev.steps⟩ }

theorem first_body_program_emits_by_construction
    (w : (Plan (G.selector ell)).Slot (exteriorChild G ell i j g)) :
    ((publicIssuedBodyProgram W C i j g pad gate writer).old w).result.issued=issuedAtFirstDepth W C i j g ∧
      ((publicIssuedBodyProgram W C i j g pad gate writer).old w).steps=(writer.old w).steps :=
  ⟨rfl,rfl⟩

/-- The stored seat key only depends on q and the selected layout width,
not on the name of the newly issued occurrence. -/
theorem first_body_issue_preserves_the_seat_key
    (w : (Plan (G.selector ell)).Slot (exteriorChild G ell i j g)) :
    occurrencePageWord (bodyAtActualSlot (literalSite W C i j g) gate pad
        (publicIssuedBodyProgram W C i j g pad gate writer) w).result=
      occurrencePageWord (bodyAtActualSlot (literalSite W C i j g) gate pad writer w).result := rfl

def ownerWordsWithPublicIssuer :
    OwnerWordsAtBodies (literalSite W C i j g) gate pad root
      (publicIssuedBodyProgram W C i j g pad gate writer) where
  width := owners.width
  name := owners.name
  distinct := owners.distinct
  keys := owners.keys
  ports := fun w =>
    let D := owners.ports w
    { seatWidth := D.seatWidth
      seats := D.seats
      queries := D.queries
      ownerQuery := D.ownerQuery
      sideExact := D.sideExact
      seatHit := D.seatHit
      seatUnique := D.seatUnique
      fallback := D.fallback }

#print axioms publicIssuedBodyProgram
#print axioms first_body_program_emits_by_construction
#print axioms first_body_issue_preserves_the_seat_key
#print axioms ownerWordsWithPublicIssuer
end
end J6R55Public


namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R14ZeroMode
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R15ModeCost J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R31RootResidentTables J6R50SourceProducer
open J6R51 J6R51Online J6R48DFS J6R54PublicFamily J6R16ModeCost
open J6R12Blueprint J6R10Reachable J6R11Blueprint J6ActiveRun J1PPrinted J6R26DescriptorTree
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R35RootOrigins J6R54ExteriorOwner
open J6R55TerminalBootJoined J6R55BootBodies J6R54TerminalBoot
open J6R51Leaf J6R50Leaf J6R53PublicMount
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 29000000
set_option maxRecDepth 4800
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {A : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) A (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew rate own : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable (pad : ℕ)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W C i j g).hf}
variable (ops : OnlineOperators T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
variable (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad)
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable {name : SourceVertex A→Word own}
variable (root : RootRoster (P:=A) gate pad name)
variable (writer : FirstBodyProgram (literalSite W C i j g) gate pad T)
variable (owners : OwnerWordsAtBodies (literalSite W C i j g) gate pad root writer)
variable (rootInj : Function.Injective name)
variable (req : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
  (Y : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
  (u : (Plan (G.selector ell)).Slot v.child), Meter (FixedRequest Y u))

variable (bp : 0<base)
variable (terminal : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
  (Y : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)), ResidentLeafData Y)

/-- No unit of execution is identified by an arbitrary substitute tree:
the driver is made with the same mounted layout and boot/read meters. The
old terminal arithmetic chart is still the one consumed by the public runner. -/
def joinedActualDriver
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val)
    (emits : ∀ w, (writer.old w).result.issued=issuedAtFirstDepth W C i j g)
    (chart : letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
      LoopCharts (literalSite W C i j g) pad
        (joinedActualPublicMachine W C i j g pad ops B gate root writer owners rootInj req sync old)
        bp terminal) :
    EmittedSiteDriver W C rate pad bp i j g := by
  let M := joinedActualPublicMachine W C i j g pad ops B gate root writer owners rootInj req sync old
  let slots := joinedSlots (literalSite W C i j g) gate pad root writer owners
  have realEmits (w : (Plan (G.selector ell)).Slot (exteriorChild G ell i j g)) :
      (slots w).occurrence.result.issued=issuedAtFirstDepth W C i j g :=
    ((replaced_boot_keeps_real_numeric_and_atlas_words (literalSite W C i j g) gate pad w (writer.old w)
      writer.lanes (writer.seats w)).2.1).trans (emits w)
  have issued := actual_machine_uses_its_two_measured_issuers W C i j g pad ops B gate root slots rootInj req sync old realEmits
  refine ⟨T,M,terminal,chart,issued.1,?_⟩
  intro x p u w
  exact issued.2 p u w

theorem joined_driver_uses_the_exact_metered_machine
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val)
    (emits : ∀ w, (writer.old w).result.issued=issuedAtFirstDepth W C i j g)
    (chart : letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
      LoopCharts (literalSite W C i j g) pad
        (joinedActualPublicMachine W C i j g pad ops B gate root writer owners rootInj req sync old)
        bp terminal) :
    (joinedActualDriver W C i j g pad ops B gate root writer owners rootInj req bp terminal sync old emits chart).source=
      joinedActualPublicMachine W C i j g pad ops B gate root writer owners rootInj req sync old :=
  rfl

#print axioms joinedActualDriver
#print axioms joined_driver_uses_the_exact_metered_machine
end
end J6R55Public


namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R14ZeroMode
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R15ModeCost J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R31RootResidentTables J6R50SourceProducer
open J6R51 J6R51Online J6R48DFS J6R54PublicFamily J6R16ModeCost
open J6R12Blueprint J6R10Reachable J6R11Blueprint J6ActiveRun J1PPrinted J6R26DescriptorTree
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R35RootOrigins J6R54ExteriorOwner
open J6R55TerminalBootJoined J6R55BootBodies J6R54TerminalBoot
open J6R51Leaf J6R50Leaf J6R53PublicMount
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 29000000
set_option maxRecDepth 4800
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {A : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) A (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew rate own : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable (pad : ℕ)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W C i j g).hf}
variable (ops : OnlineOperators T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
variable (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad)
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable {name : SourceVertex A→Word own}
variable (root : RootRoster (P:=A) gate pad name)
variable (writer : FirstBodyProgram (literalSite W C i j g) gate pad T)
variable (owners : OwnerWordsAtBodies (literalSite W C i j g) gate pad root writer)
variable (rootInj : Function.Injective name)
variable (req : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
  (Y : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
  (u : (Plan (G.selector ell)).Slot v.child), Meter (FixedRequest Y u))

variable (bp : 0<base)
variable (terminal : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
  (Y : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)), ResidentLeafData Y)

def stampedPublicMachine
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val) :
    OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate :=
  joinedActualPublicMachine W C i j g pad ops B gate root
    (publicIssuedBodyProgram W C i j g pad gate writer)
    (ownerWordsWithPublicIssuer W C i j g pad gate root writer owners) rootInj req sync old

/-- This is the precise input of `publicJobsOfEmittedDrivers`.  The body and
owner writers and the actual selected-pick recipe are evaluated by this very
machine.  Caller data does not include a first issue word or successor issue
law, a ready certificate, or a manufactured leaf agreement. -/
def stampedPublicDriver
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val)
    (chart : letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
      LoopCharts (literalSite W C i j g) pad
        (stampedPublicMachine W C i j g pad ops B gate root writer owners rootInj req sync old)
        bp terminal) :
    EmittedSiteDriver W C rate pad bp i j g :=
  joinedActualDriver W C i j g pad ops B gate root
    (publicIssuedBodyProgram W C i j g pad gate writer)
    (ownerWordsWithPublicIssuer W C i j g pad gate root writer owners) rootInj req bp terminal sync old
    (fun w=>(first_body_program_emits_by_construction W C i j g pad gate writer w).1) chart

theorem stamped_source_has_literal_boot
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val)
    (capacity : nativeDepthCapacity W C i j g) :
    ExactPrintedBoot (literalSite W C i j g)
      (stampedPublicMachine W C i j g pad ops B gate root writer owners rootInj req sync old) gate :=
  (measured_raw_boot_and_dispatch_share_the_same_ready_machine W C i j g pad ops B gate root
    (publicIssuedBodyProgram W C i j g pad gate writer)
    (ownerWordsWithPublicIssuer W C i j g pad gate root writer owners) rootInj req sync old capacity
    (fun w=>(first_body_program_emits_by_construction W C i j g pad gate writer w).1)).1

#print axioms stampedPublicMachine
#print axioms stampedPublicDriver
#print axioms stamped_source_has_literal_boot
end
end J6R55Public

