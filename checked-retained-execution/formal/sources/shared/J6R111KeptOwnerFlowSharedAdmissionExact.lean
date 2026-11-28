import J6R111KeptOwnerFlowSharedAdmission
import J6R108FinalDriverReady

/-! At the prescribed row, relate the very site returned by the one
paid admission to the captured query head. All equalities below are
proofs, not operations that emit another row or atlas. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R33StatefulArithmeticPage J6R57PublicRequest
open J6R31RootResidentTables J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R55Public J6R75OuterTime J6R108FinalDriver J6R64Active
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22500000
set_option maxRecDepth 5000
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (C : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W C)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable (H : ExactHead m native tc tj tw i j)
variable (same : H=(prepareHead W i j).result)

include same in
theorem actual_canonical_admission_keeps_the_exact_site_from_that_head
    (sync : B.synced) (reserved : ∀ x∈B.headers,x.id.bits.take kp≠C.mark.bits) :
    let program := submitResidentRowKeepingSite C S pad B (sourceRow (W:=W) C i j g)
    ∃ A : ResidentAdmissionCarry (W:=W) C pad,
      program.result=some A ∧ A.row=sourceRow (W:=W) C i j g ∧ A.site=(siteFromHead W g C H).result ∧
      (submitResidentRow C S pad B (sourceRow (W:=W) C i j g)).result=some (A.receipt.1,true) ∧
      IsLive (A.site.seed pad) A.receipt.1 ∧ OwnsHeader A.site.header.result A.receipt.1 := by
  let row := sourceRow (W:=W) C i j g
  let probe := S.requests.probes.read j
  let Q := readPublicRequest C S.requests row.wire probe.result.val
  obtain ⟨_,ht,hj,hg,_,_⟩ := actual_entry_wires W C.mark ((i,j),g)
  have hit : Q.result=some row :=
    (true_prescribed_address_is_found C S.requests row.wire ((i,j),g) ht hj hg probe.result.val (S.requests.probes.consistent j)).1
  have kept := retaining_the_paid_site_opens_one_root_atlas C S pad B row row hit
  let X := (entrySource (W:=W) C row).result
  let install := (cachedJobFromSource C S pad row X rfl).install B
  let A : ResidentAdmissionCarry (W:=W) C pad := ⟨row,X,install.result,rfl⟩
  have out : (submitResidentRowKeepingSite C S pad B row).result=some A := congrArg Meter.result kept
  have measure := (retained_admission_projects_to_actual_ack_and_one_new_handle_charge C S pad B row).1
  have returns : (submitResidentRow C S pad B row).result=some A.receipt :=
    measure.symm.trans (congrArg (Option.map ResidentAdmissionCarry.receipt) out)
  have ok : A.receipt.2=true := by
    obtain ⟨bank,ack,_,_⟩ := generated_public_row_returns_live_original_bank C S pad B
      sync reserved row (canonical_source_row_is_resident C S i j g)
    exact congrArg Prod.snd (Option.some.inj (returns.symm.trans ack))
  have ack : (submitResidentRow C S pad B row).result=some (A.receipt.1,true) :=
    returns.trans (congrArg some (Prod.ext rfl ok))
  have live := actual_public_return_owns_its_literal_seed_and_header C S pad B i j g sync reserved A.receipt.1 ack
  have x : A.site=literalSite W C i j g := rfl
  have sameHead : A.site=(siteFromHead W g C H).result := by rw [same]; exact x
  refine ⟨A,out,rfl,sameHead,ack,?_,?_⟩
  · rw [x]; exact live.1
  · rw [x]; exact live.2

#print axioms actual_canonical_admission_keeps_the_exact_site_from_that_head
end
end J6R111KeptOwnerFlow

