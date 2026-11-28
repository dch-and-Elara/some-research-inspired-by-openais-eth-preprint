import J6R108FinalDriverMachine


/-! Build the selected group plan using a bank value actually returned
by the literal request. Its Ready field is derived from the two actual
issued meters. The same native R102 body, true source owner callback
and existing R68 selected layout are the ones installed in the plan. -/
namespace J6R108FinalDriver
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R66.BootPeak J6R57Public

open J6R75OuterTime J6R14ZeroMode J6R55Public
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 1600000
set_option pp.maxSteps 1100
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable {rate : ℕ}
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W D i j g).hf}


variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)
variable (baseMachine : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
variable (A : FirstBodyProgram (literalSite W D i j g) gate pad T)
variable (owners : OwnerWordsAtBodies (literalSite W D i j g) gate pad root A)
variable (rootInj : Function.Injective rootName)

theorem this_paid_native_code_driver_is_ready
    (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (live : IsLive ((literalSite W D i j g).seed pad) bank)
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (old : ∀ row∈prior.headers,row.id.val ≤ D.mark.val) (capacity : nativeDepthCapacity W D i j g)
    (first : ∀ w : (Plan (G.selector ell)).Slot ((exteriorChild G ell i j g)),
      (A.old w).result.issued=issuedAtFirstDepth W D i j g)
    (next : ∀ {v : Ticket (G.selector ell) ((exteriorChild G ell i j g))}
      (Y : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
      (w : (Plan (G.selector ell)).Slot v.child),
      (baseMachine.demand Y w).result.event.issued=increment Y.birth.job.identifier)
    (ack : (submitResidentRow D S pad prior ((sourceRow (W:=W) D i j g))).result=some (bank,true)) :
    ReadyOnStack (borns (paidCodeAtReturnedBank D pad i j g gate root baseMachine A owners rootInj bank live)) bank := by
  let actual := paidCodeAtReturnedBank D pad i j g gate root baseMachine A owners rootInj bank live
  have exactIssuers : UsesFirstIssuer actual (issuedAtFirstDepth W D i j g) ∧ UsesChildIncrement actual := by
    change UsesFirstIssuer (withMeteredNativeCode (literalSite W D i j g) gate pad A root baseMachine owners bank live rootInj)
      (increment ((literalSite W D i j g).issue.result)) ∧
      UsesChildIncrement (withMeteredNativeCode (literalSite W D i j g) gate pad A root baseMachine owners bank live rootInj)
    exact actual_paid_code_machine_uses_the_two_raw_issuers (literalSite W D i j g) gate pad root baseMachine
      A owners bank live rootInj first next
  have found := ready_and_live_on_the_same_actual_returned_bank D S pad prior i j g actual sync reserved old capacity
    exactIssuers.1 exactIssuers.2 bank ack
  intro c p w
  exact found.1 p w

#print axioms this_paid_native_code_driver_is_ready
end
end J6R108FinalDriver

