import J6R55PublicDrivers
import J6R55TerminalOriginExterior

/-! Exact public acquisition without a template initial/demand machine:
the first slot uses the actual post-mount origin producer, and every
non-first load consumes the single-pick incrementing dispatcher. -/
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
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 4500
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
variable (slots : ∀ w : (Plan (G.selector ell)).Slot (exteriorChild G ell i j g),
  LiteralFirstSlot (literalSite W C i j g) gate pad root w T)
variable (rootInj : Function.Injective name)
variable (req : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
  (Y : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
  (u : (Plan (G.selector ell)).Slot v.child), Meter (FixedRequest Y u))

def actualPublicMachine
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val) :
    OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate :=
  let X := literalSite W C i j g
  let bank := actualInstalledBank W C i j g pad B
  let live := (real_public_install_and_reserve W C i j g pad B sync old).2.1
  let boot := fun w=>assembleFirstExterior X gate pad root w (slots w) bank live rootInj
  fromActualInputMeters ops boot req

theorem actual_machine_boot_is_the_measured_occurrence
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val)
    (w : (Plan (G.selector ell)).Slot (exteriorChild G ell i j g)) :
    ((actualPublicMachine W C i j g pad ops B gate root slots rootInj req sync old).initial w).result.input=
      (slots w).occurrence.result := by
  exact actual_first_exterior_occurrence (literalSite W C i j g) gate pad root w (slots w)
    (actualInstalledBank W C i j g pad B)
    (real_public_install_and_reserve W C i j g pad B sync old).2.1 rootInj

theorem actual_machine_uses_its_two_measured_issuers
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val)
    (emits : ∀ w, (slots w).occurrence.result.issued=issuedAtFirstDepth W C i j g) :
    let real := actualPublicMachine W C i j g pad ops B gate root slots rootInj req sync old
    UsesFirstIssuer real (issuedAtFirstDepth W C i j g) ∧ UsesChildIncrement real := by
  let real := actualPublicMachine W C i j g pad ops B gate root slots rootInj req sync old
  refine ⟨?_,?_⟩
  · exact real_first_issuer_from_exact_boot W C i j g pad real (fun w=>(slots w).occurrence)
      (actual_machine_boot_is_the_measured_occurrence W C i j g pad ops B gate root slots rootInj req sync old) emits
  · intro c p u w
    exact selected_demand_uses_real_increment (req (sourceState real p u) w)

theorem actual_machine_has_no_ready_input
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val)
    (capacity : nativeDepthCapacity W C i j g)
    (emits : ∀ w, (slots w).occurrence.result.issued=issuedAtFirstDepth W C i j g) :
    let real := actualPublicMachine W C i j g pad ops B gate root slots rootInj req sync old
    ReadyOnStack (borns real) (actualInstalledBank W C i j g pad B) := by
  let real := actualPublicMachine W C i j g pad ops B gate root slots rootInj req sync old
  have issuers := actual_machine_uses_its_two_measured_issuers W C i j g pad ops B gate root slots rootInj req sync old emits
  have claim := real_ready_after_literal_mount W C i j g pad real B sync old capacity issuers.1 issuers.2
  change ReadyOnStack (borns real) _
  intro c p w
  exact claim.1 p w

#print axioms actualPublicMachine
#print axioms actual_machine_boot_is_the_measured_occurrence
#print axioms actual_machine_uses_its_two_measured_issuers
#print axioms actual_machine_has_no_ready_input
end
end J6R55Public

