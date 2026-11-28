import J6R66BootPeakAtlas
import J6R59PublicAdmittedRead

/-! The only external install on a successful R57 request is the real
cached atlas job. Identify the actual bank passed forward with this
published state, including its precisely added serialized fields. -/
namespace J6R66.BootPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R48DFS J6R33StatefulArithmeticPage J6R30ProducedGateRegistry J6R51Peak
open J6R59Public J6R21Ancestor J6R32StatefulArithmetic
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
set_option maxRecDepth 4750
set_option Elab.async false

def frameWordsBits {f : ℤ[X]} {prec : ℕ} (S : FrameShape f prec) : ℕ :=
  S.birth.bits.length+bitSize Subtype.val S.old

def bankFrameBits {f : ℤ[X]} {ell key prec tw bw page : ℕ}
    (B : PageBank f ell key prec tw bw page) : ℕ :=
  (B.records.map (fun row=>frameWordsBits row.payload.payload.shape)).sum

def mountedSelectedBits {f : ℤ[X]} {ell key prec tw bw page : ℕ}
    (B : PageBank f ell key prec tw bw page) : ℕ :=
  directoryBits B+residentAtlasBits B+bankFrameBits B

def mountedInsertionBits {f : ℤ[X]} {ell key prec tw bw page : ℕ}
    (J : PageJob f ell key prec tw bw page) : ℕ :=
  insertionBits J+((envelopePages J.expected).map List.length).sum+frameWordsBits J.expected.shape

theorem publication_adds_exact_selected_record
    {f : ℤ[X]} {ell key prec tw bw page : ℕ}
    (B : PageBank f ell key prec tw bw page) (J : PageJob f ell key prec tw bw page) :
    mountedSelectedBits (afterOne B J)=mountedSelectedBits B+mountedInsertionBits J := by
  have D := one_publication_adds_exact_directory_bits B J
  have E : residentAtlasBits (afterOne B J)=
      ((envelopePages J.expected).map List.length).sum+residentAtlasBits B := rfl
  have F : bankFrameBits (afterOne B J)=frameWordsBits J.expected.shape+bankFrameBits B := rfl
  unfold mountedSelectedBits mountedInsertionBits
  rw [D,E,F]
  ac_rfl

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (r : Entry D.mark m native tc tj tw)

theorem accepted_entry_installs_that_actual_job
    (sync : B.synced) (reserved : ∀ x∈B.headers,x.id.bits.take kp≠D.mark.bits)
    (stored : r∈S.requests.rows) :
    let X := (entrySource (W:=W) D r).result
    let job := cachedExteriorJob D S pad r
    (submitResidentRow D S pad B r).result=some (afterOne B job,true) ∧
    IsLive (X.seed pad) (afterOne B job) ∧
    mountedSelectedBits (afterOne B job)=mountedSelectedBits B+mountedInsertionBits job := by
  rw [S.requests.ordered,(catalogue_exact_order_and_bill W D.mark).1] at stored
  obtain ⟨x,_,hx⟩ := List.mem_map.mp stored
  subst r
  let r := (emitAt W D.mark x).result
  let X := (entrySource (W:=W) D r).result
  let job := cachedExteriorJob D S pad r
  let same := S.exactRoot.trans (congrArg Meter.result (one_root_cache_for_every_entry (W:=W) D r))
  obtain ⟨_,t,j,g,_,_⟩ := actual_entry_wires W D.mark x
  have marker : X.issue.result.bits.take kp=D.mark.bits :=
    actual_public_owner_marker W D x.1.1 x.1.2 x.2
  have jobId : job.identifier=(X.seed pad).identifier := (same_seed_bytes X S.root same pad).2.1
  have fresh : ∀ row∈B.headers,row.id≠(X.seed pad).identifier := by
    intro row inBank sameID
    apply reserved row inBank
    rw [sameID]
    change X.header.result.id.bits.take kp=D.mark.bits
    rw [(stable_exterior_header X).1,marker]
  have pub := paid_job_mounts_the_same_selected_directory B job sync
    (fun row hr h=>fresh row hr (h.trans jobId))
  have matched : (job.install B).result=((X.seed pad).install B).result :=
    (prepared_seed_exact_install X S.root same pad B sync fresh).1
  have step : (job.install B).result=(afterOne B job,true) :=
    congrArg Meter.result pub.1
  have source := a_true_address_mounts_the_original_native_seed D S pad B sync reserved
    r.wire x t j g (S.requests.probes.read x.1.2).result.val (S.requests.probes.consistent x.1.2)
  have accepted : (submitResidentRow D S pad B r).result=some ((X.seed pad).install B).result := source.1
  have hit : (submitResidentRow D S pad B r).result=some (afterOne B job,true) :=
    accepted.trans (congrArg some (matched.symm.trans step))
  have actual : IsLive job (afterOne B job) := new_is_live job B
  have live : IsLive (X.seed pad) (afterOne B job) :=
    (prepared_seed_same_live X S.root same pad (afterOne B job)).mp actual
  exact ⟨hit,live,publication_adds_exact_selected_record B job⟩

variable {Out : Type} (go : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→Meter Out)
variable (bad : Meter Out)

theorem actual_external_callback_uses_counted_bank
    (sync : B.synced) (reserved : ∀ x∈B.headers,x.id.bits.take kp≠D.mark.bits)
    (stored : r∈S.requests.rows) :
    let job := cachedExteriorJob D S pad r
    let X := (entrySource (W:=W) D r).result
    let after := afterOne B job
    let scan := S.requests.probes.read r.coord.1.2
    IsLive (X.seed pad) after ∧
    useAdmittedResidentRow D S pad B r go bad=
      ⟨(go after).result,(submitResidentRow D S pad B r).steps+(go after).steps+4⟩ ∧
    scan.result.val.length=f.natDegree ∧
    mountedSelectedBits after=mountedSelectedBits B+mountedInsertionBits job := by
  have actual := accepted_entry_installs_that_actual_job D S pad B r sync reserved stored
  refine ⟨actual.2.1,?_,(S.requests.probes.read r.coord.1.2).result.property,actual.2.2⟩
  unfold useAdmittedResidentRow
  dsimp only
  rw [actual.1]

#print axioms publication_adds_exact_selected_record
#print axioms accepted_entry_installs_that_actual_job
#print axioms actual_external_callback_uses_counted_bank
end
end J6R66.BootPeak
