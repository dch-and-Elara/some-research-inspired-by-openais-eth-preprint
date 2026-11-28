import J6R66BootPeakMount
import J6R64ActiveIncoming

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3200
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Run the raw-centre R68 contraction on the *returned* bank of the
actual R57 publication. The bank in the proof is merely the verified
normal form of that publication; its installer is not called twice. -/
namespace J6R75OuterTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R48DFS J6R33StatefulArithmeticPage J6R30ProducedGateRegistry J6R51Peak
open J6R59Public J6R21Ancestor J6R32StatefulArithmetic J6ActiveRun J6R24MeteredRecursion
open J6R64Active J6R66.BootPeak J6R11Blueprint J6R32RootGeneratedRegistryInputs

theorem own_header_after_immutable_prepend {key prec tw bw : ℕ} {Data : Type*}
    (B : Ledger key prec tw bw Data) (job : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) Data)
    (head : DirRow key) (eq : job.entry.result=head) :
    OwnsHeader head (afterOne B job) := by
  unfold OwnsHeader afterOne
  exact congrArg some eq

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

abbrev actualExterior : StableExterior G ell q rr cc dd edgew tc tj Key prec tw bw :=
  (entrySource (W:=W) D row).result
local notation "X" => (actualExterior (W:=W) D row)
abbrev rawCall : Call (PhysicalHost f ell) := exteriorChild G ell (X).centre (X).sample (X).group
local notation "Ext" => (rawCall (W:=W) D row)

abbrev publishedBank (S0 : InstalledRequestInputs W D) (p : ℕ)
    (prior : PageBank f ell Key prec tw bw (pageKeyWidth m+p)) (r : Entry D.mark m native tc tj tw) :
    PageBank f ell Key prec tw bw (pageKeyWidth m+p) :=
  afterOne prior (cachedExteriorJob D S0 p r)
local notation "Live" => (publishedBank D S pad B row)

theorem selected_job_header_is_literal :
    (cachedExteriorJob D S pad row).entry.result=(X).header.result := by
  let Y := (entrySource (W:=W) D row).result
  let same : S.root=(rootPreparationFor Y).result :=
    S.exactRoot.trans (congrArg Meter.result (one_root_cache_for_every_entry (W:=W) D row))
  exact (same_seed_bytes Y S.root same pad).1

theorem published_head_is_the_actual_raw_header
    (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (r : Entry D.mark m native tc tj tw) :
    OwnsHeader (entrySource (W:=W) D r).result.header.result
      (afterOne prior (cachedExteriorJob D S pad r)) := by
  exact own_header_after_immutable_prepend prior (cachedExteriorJob D S pad r)
    (entrySource (W:=W) D r).result.header.result (selected_job_header_is_literal D S pad r)


#print axioms own_header_after_immutable_prepend
#print axioms actualExterior
#print axioms rawCall
#print axioms publishedBank
#print axioms J6R35GatewayPreparation.same_seed_bytes
#print axioms J6R57PublicRequest.one_root_cache_for_every_entry
#print axioms J6R64Active.OwnsHeader
#print axioms selected_job_header_is_literal
#print axioms published_head_is_the_actual_raw_header
end
end J6R75OuterTime

