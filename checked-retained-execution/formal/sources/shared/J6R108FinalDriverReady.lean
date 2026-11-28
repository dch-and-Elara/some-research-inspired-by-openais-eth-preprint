import J6R108FinalDriverIssuer
import J6R75OuterTimeSlotData

/-! Readiness belongs to the ACTUAL bank returned by the literal R57
admission. The R55 bank is compared at its acknowledged value only.
The proof performs no additional publication and transports no fee. -/
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
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R57ScopeFee
open J6R75OuterTime J6R14ZeroMode J6R55Public

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 22000000
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
local notation "Row" => (sourceRow (W:=W) D i j g)
local notation "X" => (literalSite W D i j g)

theorem the_actual_R57_reply_has_the_R55_installed_bank
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (ack : (submitResidentRow D S pad prior (Row)).result=some (bank,true)) :
    bank=actualInstalledBank W D i j g pad prior := by
  let r := sourceRow (W:=W) D i j g
  let probe := S.requests.probes.read j
  obtain ⟨_,ht,hj,hg,_,_⟩ := actual_entry_wires W D.mark ((i,j),g)
  have ret := (a_true_address_mounts_the_original_native_seed D S pad prior sync reserved r.wire
    ((i,j),g) ht hj hg probe.result.val (S.requests.probes.consistent j)).1
  change (submitResidentRow D S pad prior r).result=some ((((X).seed pad).install prior).result) at ret
  change bank=(((X).seed pad).install prior).result.1
  exact congrArg Prod.fst (Option.some.inj (ack.symm.trans ret))

theorem the_actual_R57_reply_is_the_proof_only_published_snapshot
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (ack : (submitResidentRow D S pad prior (Row)).result=some (bank,true)) :
    bank=publishedBank D S pad prior (Row) := by
  have stated := (accepted_entry_installs_that_actual_job D S pad prior (Row) sync reserved
    (canonical_source_row_is_resident D S i j g)).1
  exact congrArg Prod.fst (Option.some.inj (ack.symm.trans stated))

theorem actual_public_return_owns_its_literal_seed_and_header
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (ack : (submitResidentRow D S pad prior (Row)).result=some (bank,true)) :
    IsLive ((X).seed pad) bank ∧ OwnsHeader (X).header.result bank := by
  have hExpected := the_actual_R57_reply_is_the_proof_only_published_snapshot D S pad prior i j g sync reserved bank ack
  rw [hExpected]
  exact ⟨(accepted_entry_installs_that_actual_job D S pad prior (Row) sync reserved
    (canonical_source_row_is_resident D S i j g)).2.1,
    published_head_is_the_actual_raw_header D S pad prior (Row)⟩

theorem ready_and_live_on_the_same_actual_returned_bank
    (M : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (old : ∀ row∈prior.headers,row.id.val ≤ D.mark.val) (capacity : nativeDepthCapacity W D i j g)
    (first : UsesFirstIssuer M (issuedAtFirstDepth W D i j g)) (next : UsesChildIncrement M)
    (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (ack : (submitResidentRow D S pad prior (Row)).result=some (bank,true)) :
    ReadyOnStack (borns M) bank ∧ IsLive ((X).seed pad) bank ∧ OwnsHeader (X).header.result bank := by
  have hInstalled := the_actual_R57_reply_has_the_R55_installed_bank D S pad prior i j g sync reserved bank ack
  have hExpected := the_actual_R57_reply_is_the_proof_only_published_snapshot D S pad prior i j g sync reserved bank ack
  have ready : ReadyOnStack (borns M) bank := by
    rw [hInstalled]
    exact (real_ready_after_literal_mount W D i j g pad M prior sync old capacity first next).1
  have same := accepted_entry_installs_that_actual_job D S pad prior (Row) sync reserved
    (canonical_source_row_is_resident D S i j g)
  have live : IsLive ((X).seed pad) bank := by rw [hExpected]; exact same.2.1
  have owns : OwnsHeader (X).header.result bank := by
    rw [hExpected]
    exact published_head_is_the_actual_raw_header D S pad prior (Row)
  exact ⟨ready,live,owns⟩

#print axioms the_actual_R57_reply_has_the_R55_installed_bank
#print axioms the_actual_R57_reply_is_the_proof_only_published_snapshot
#print axioms actual_public_return_owns_its_literal_seed_and_header
#print axioms ready_and_live_on_the_same_actual_returned_bank
end
end J6R108FinalDriver

