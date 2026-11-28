import J6R75OuterTimeHead

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 9000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! The caller's peeled sample bytes go to the actual R57 server gate.
There is no additional client read from submitResidentRow. -/
namespace J6R75OuterTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R48DFS J6R33StatefulArithmeticPage J6R30ProducedGateRegistry J6R51Peak
open J6R59Public J6R21Ancestor J6R32StatefulArithmetic J6ActiveRun J6R24MeteredRecursion
open J6R64Active J6R66.BootPeak J6R11Blueprint J6R32RootGeneratedRegistryInputs

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
local notation "Key" => (KeyWidth kp tc tj)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell Key prec tw bw Pg)
local notation "Job" => (PageJob f ell Key prec tw bw Pg)
variable (B : Bank) (row : Entry D.mark m native tc tj tw)



theorem stored_outer_row_is_the_actual_raw_selection (stored : row∈S.requests.rows) :
    (rawRequest D.mark row.wire S.requests.rows).result=some row := by
  rw [S.requests.ordered,(catalogue_exact_order_and_bill W D.mark).1] at stored
  obtain ⟨x,_,equal⟩ := List.mem_map.mp stored
  subst row
  rw [S.requests.ordered]
  obtain ⟨_,t,j,g,_,_⟩ := actual_entry_wires W D.mark x
  exact (native_raw_request_hit W D.mark _ x t j g).1

theorem accepted_ack_uses_the_original_probe
    (prior : Bank) (r : Entry D.mark m native tc tj tw)
    (written : r∈S.requests.rows)
    (raw : List Bool) (ok : (admitRequest D S pad prior r.wire raw).result.isSome) :
    raw=List.ofFn ((rootPreset G ell).word r.coord.1.2) := by
  have hit := stored_outer_row_is_the_actual_raw_selection D S r written
  have test : (readPublicRequest D S.requests r.wire raw).result.isSome := by
    cases H : (readPublicRequest D S.requests r.wire raw).result with
    | none =>
      unfold admitRequest at ok
      dsimp only at ok
      rw [H] at ok
      cases ok
    | some v => rfl
  unfold readPublicRequest at test
  dsimp only at test
  rw [hit] at test
  exact (prescribed_sample_accepted D S.requests r raw).mp test

theorem legal_raw_admission_is_the_same_publication
    (prior : Bank) (r : Entry D.mark m native tc tj tw)
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (written : r∈S.requests.rows)
    (raw : List Bool) (legal : raw=List.ofFn ((rootPreset G ell).word r.coord.1.2)) :
    (admitRequest D S pad prior r.wire raw).result=some (publishedBank D S pad prior r,true) := by
  have h : raw=(S.requests.probes.read r.coord.1.2).result.val :=
    legal.trans (S.requests.probes.consistent _).symm
  rw [h]
  exact (accepted_entry_installs_that_actual_job D S pad prior r sync reserved written).1

theorem legal_submit_has_the_extra_client_read
    (prior : Bank) (r : Entry D.mark m native tc tj tw)
    (raw : List Bool) (legal : raw=List.ofFn ((rootPreset G ell).word r.coord.1.2)) :
    (submitResidentRow D S pad prior r).steps=
      (S.requests.probes.read r.coord.1.2).steps+
        (admitRequest D S pad prior r.wire raw).steps+3 := by
  have h : raw=(S.requests.probes.read r.coord.1.2).result.val :=
    legal.trans (S.requests.probes.consistent _).symm
  unfold submitResidentRow
  dsimp only
  rw [h]

theorem peeled_admission_charges_the_real_lookup_sample_and_install
    (prior : Bank) (r : Entry D.mark m native tc tj tw)
    (written : r∈S.requests.rows) (raw : List Bool)
    (legal : raw=List.ofFn ((rootPreset G ell).word r.coord.1.2)) :
    let wanted := S.requests.probes.read r.coord.1.2
    let looked := rawRequest D.mark r.wire S.requests.rows
    let test := eqRawBits raw wanted.result.val
    let extRun := entrySource (W:=W) D r
    let job := cachedExteriorJob D S pad r
    (admitRequest D S pad prior r.wire raw).steps=
      looked.steps+wanted.steps+test.steps+extRun.steps+(job.install prior).steps+11 := by
  let want := S.requests.probes.read r.coord.1.2
  let looked := rawRequest D.mark r.wire S.requests.rows
  have found := stored_outer_row_is_the_actual_raw_selection D S r written
  have good : (eqRawBits raw want.result.val).result=true :=
    (eq_raw_bits_exact raw want.result.val).1.mpr (legal.trans (S.requests.probes.consistent _).symm)
  have returned : (readPublicRequest D S.requests r.wire raw).result=some r := by
    unfold readPublicRequest gateSample
    dsimp only
    rw [found]
    change (if (eqRawBits raw want.result.val).result then some r else none)=some r
    rw [if_pos good]
  have cost : (readPublicRequest D S.requests r.wire raw).steps=
      looked.steps+want.steps+(eqRawBits raw want.result.val).steps+7 := by
    unfold readPublicRequest gateSample
    dsimp only
    rw [found]
    change looked.steps+(want.steps+(eqRawBits raw want.result.val).steps+4)+3=_
    omega
  dsimp only
  rw [admission_runs_actual_selected_job D S pad prior r.wire raw r returned,cost]
  change looked.steps+want.steps+(eqRawBits raw want.result.val).steps+7+
      (entrySource (W:=W) D r).steps+((cachedExteriorJob D S pad r).install prior).steps+4=
    looked.steps+want.steps+(eqRawBits raw want.result.val).steps+
      (entrySource (W:=W) D r).steps+((cachedExteriorJob D S pad r).install prior).steps+11
  omega

theorem any_accepted_live_bank_is_this_actual_bank
    (prior : Bank) (r : Entry D.mark m native tc tj tw)
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (written : r∈S.requests.rows) (raw : List Bool) {found : Bank}
    (hit : (admitRequest D S pad prior r.wire raw).result=some (found,true)) :
    found=publishedBank D S pad prior r := by
  have ok : (admitRequest D S pad prior r.wire raw).result.isSome := by simp [hit]
  have known := legal_raw_admission_is_the_same_publication D S pad prior r sync reserved written raw
    (accepted_ack_uses_the_original_probe D S pad prior r written raw ok)
  exact congrArg Prod.fst (Option.some.inj (hit.symm.trans known))

/-- Match the actual success word, not the raw bytes a second time. -/
def followAck {L Out : Type*} (A : Meter (Option (L×Bool))) (P : L→Prop)
    (good : ∀ b,A.result=some (b,true)→P b)
    (go : (b : L)→P b→Meter Out) (bad : Meter Out) : Meter Out :=
  match hit : A.result with
  | some (b,true) =>
    let R := go b (good b hit)
    ⟨R.result,A.steps+R.steps+4⟩
  | _ => ⟨bad.result,A.steps+bad.steps+4⟩

theorem follow_ack_exact {L Out : Type*} (A : Meter (Option (L×Bool))) (P : L→Prop)
    (good : ∀ b,A.result=some (b,true)→P b)
    (go : (b : L)→P b→Meter Out) (bad : Meter Out) {b : L}
    (hit : A.result=some (b,true)) :
    followAck A P good go bad=
      ⟨(go b (good b hit)).result,A.steps+(go b (good b hit)).steps+4⟩ := by
  cases A with
  | mk x fee =>
    change x=some (b,true) at hit
    subst x
    rfl


#print axioms stored_outer_row_is_the_actual_raw_selection
#print axioms accepted_ack_uses_the_original_probe
#print axioms legal_raw_admission_is_the_same_publication
#print axioms legal_submit_has_the_extra_client_read
#print axioms peeled_admission_charges_the_real_lookup_sample_and_install
#print axioms any_accepted_live_bank_is_this_actual_bank
#print axioms follow_ack_exact
end
end J6R75OuterTime

