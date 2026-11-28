import J6R111KeptOwnerFlowSharedAdmissionExact
import J6R114EmittedReceipts

/-! Keep the actual descriptor and bank returned by the only submission.
All readback, live-root and address proofs are about this returned record. -/
namespace J6R114PrescribedReceipts
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6Mesh J6OrientedHost J6OrientedHostEval
open J6R24MeteredRecursion J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R28GeneratedRootFrame J6R54PublicFamily J6R57PublicRequest J6R52FreshExterior
open J6R34OfficialGateway J6R36SharedGateway J6R15ModeCost J6R25StableCensus
open J6R33OriginalJ6 J6R22RootReadout J6R11Repack J6R19Retained J6R12Blueprint
open J6R75OuterTime J6R31RootResidentTables J6R14ZeroMode J6R50SourceProducer J1PPrinted
open J6R51Online J6R49Cost J6R10Reachable J6R24LegalLayout
open J6R111KeptOwnerFlow J6R34RootAtlas J6R33StatefulArithmeticPage J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R35GatewayPreparation J6R64Active

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4900
set_option maxHeartbeats 24000000

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (sync : B.synced) (reserved : ∀ h∈B.headers,h.id.bits.take kp≠D.mark.bits)

structure AdmittedAtAddress
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (r : Entry D.mark m native tc tj tw) : Type where
  payload : ResidentAdmissionCarry (W:=W) D pad
  result : (submitResidentRowKeepingSite D S pad B r).result=some payload
  sameRow : payload.row=r
  selectedSite : payload.site=(siteFromHead W g D (prepareHead W i j).result).result
  originalAck : (submitResidentRow D S pad B r).result=some (payload.receipt.1,true)
  live : IsLive (payload.site.seed pad) payload.receipt.1
  owns : OwnsHeader payload.site.header.result payload.receipt.1

include sync reserved in
theorem all_published_addresses_admit_their_exact_bound_payload
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (r : Entry D.mark m native tc tj tw) (sameRow : r=sourceRow (W:=W) D i j g) :
    ∃ a : ResidentAdmissionCarry (W:=W) D pad,
      (submitResidentRowKeepingSite D S pad B r).result=some a ∧
      a.row=r ∧ a.site=(siteFromHead W g D (prepareHead W i j).result).result ∧
      (submitResidentRow D S pad B r).result=some (a.receipt.1,true) ∧
      IsLive (a.site.seed pad) a.receipt.1 ∧ OwnsHeader a.site.header.result a.receipt.1 := by
  subst r
  exact actual_canonical_admission_keeps_the_exact_site_from_that_head D S pad B i j g
    (prepareHead W i j).result rfl sync reserved

def admitTheEmittedRow
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (r : Entry D.mark m native tc tj tw) (sameRow : r=sourceRow (W:=W) D i j g) :
    Meter (AdmittedAtAddress D S pad B i j g r) :=
  let executed := submitResidentRowKeepingSite D S pad B r
  have good := all_published_addresses_admit_their_exact_bound_payload D S pad B sync reserved i j g r sameRow
  have success : executed.result.isSome = true := by
    obtain ⟨a,yes,_⟩ := good
    change executed.result=some a at yes
    simp [yes]
  let payload := executed.result.get success
  have arrived : executed.result=some payload := (Option.some_get success).symm
  have truth : payload.row=r ∧ payload.site=(siteFromHead W g D (prepareHead W i j).result).result ∧
      (submitResidentRow D S pad B r).result=some (payload.receipt.1,true) ∧
      IsLive (payload.site.seed pad) payload.receipt.1 ∧
      OwnsHeader payload.site.header.result payload.receipt.1 := by
    obtain ⟨a,yes,verified⟩ := good
    change executed.result=some a at yes
    have e : payload=a := Option.some.inj (arrived.symm.trans yes)
    simpa only [e] using verified
  ⟨⟨payload,arrived,truth.1,truth.2.1,truth.2.2.1,truth.2.2.2.1,truth.2.2.2.2⟩,executed.steps⟩

abbrev OnTheReturnedPayload :=
  ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (r : Entry D.mark m native tc tj tw), AdmittedAtAddress D S pad B i j g r →
    GroupReceipt (ell:=ell) G D.hf i j g

def consumeTheActualAdmittedRows (use : OnTheReturnedPayload D S pad B) : AtWrittenRow D S :=
  fun i j g r sameRow _ =>
    let a := admitTheEmittedRow D S pad B sync reserved i j g r sameRow
    let out := use i j g r a.result
    ⟨out.frame,⟨out.run.result,a.steps+out.run.steps+3⟩,out.truth⟩

theorem the_outer_group_reuses_the_site_without_a_second_paid_admission
    (use : OnTheReturnedPayload D S pad B)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (r : Entry D.mark m native tc tj tw) (sameRow : r=sourceRow (W:=W) D i j g)
    (written : r∈S.requests.rows) :
    let a := admitTheEmittedRow D S pad B sync reserved i j g r sameRow
    let out := use i j g r a.result
    ((consumeTheActualAdmittedRows D S pad B sync reserved use i j g r sameRow written).run).steps =
      (submitResidentRow D S pad B r).steps+3+out.run.steps+3 := by
  let out := use i j g r (admitTheEmittedRow D S pad B sync reserved i j g r sameRow).result
  change (submitResidentRowKeepingSite D S pad B r).steps+out.run.steps+3=_
  rw [(retained_admission_projects_to_actual_ack_and_one_new_handle_charge D S pad B r).2]

#print axioms admitTheEmittedRow
#print axioms the_outer_group_reuses_the_site_without_a_second_paid_admission
end
end J6R114PrescribedReceipts

