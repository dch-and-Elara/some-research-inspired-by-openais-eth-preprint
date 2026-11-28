import J6R67BootPeakCore
import J6R66BootPeakNativeCap

/-! Outer, successful R57 boundary values. The Page-compiler observer
is on the actual request file, actual native output, and exact widened
return of this selected job, not on another atlas with the same count. -/
namespace J6R67.BootPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R48DFS J6R33StatefulArithmeticPage J6R30ProducedGateRegistry J6R51Peak
open J6R59Public J6R21Ancestor J6R32StatefulArithmetic J6R66.BootPeak
open J6R33PageIndexedBirth
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11200000
set_option maxRecDepth 4350
set_option Elab.async false

structure ExteriorPoint where
  requests : ℕ
  nativeRows : ℕ
  widenedRows : ℕ
  header : ℕ

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P₀ : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P₀ (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {I : SharedInputs G ell q rr cc dd prec kp bw}

structure PublicRoot (image : RequestImage W I) (pad : ℕ) where
  incoming : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)
  selected : Entry image.compiled.mark m native tc tj tw
  synch : incoming.synced
  reserved : ∀ x∈incoming.headers,x.id.bits.take kp≠image.compiled.mark.bits
  stored : selected∈image.tables.requests.rows

variable {image : RequestImage W I} {pad : ℕ}
variable (Q : PublicRoot image pad)

abbrev PublicRoot.exterior :=
  (entrySource (W:=W) image.compiled Q.selected).result

abbrev PublicRoot.outerJob :=
  cachedExteriorJob image.compiled image.tables pad Q.selected

def PublicRoot.liveBank :=
  afterOne Q.incoming Q.outerJob

theorem PublicRoot.live : IsLive (Q.exterior.seed pad) Q.liveBank :=
  (accepted_entry_installs_that_actual_job image.compiled image.tables pad Q.incoming Q.selected
    Q.synch Q.reserved Q.stored).2.1

def PublicRoot.submit :=
  submitResidentRow image.compiled image.tables pad Q.incoming Q.selected

theorem actual_outer_bank_census :
    Q.submit.result=some (Q.liveBank,true) ∧
    mountedSelectedBits Q.liveBank=mountedSelectedBits Q.incoming+mountedInsertionBits Q.outerJob := by
  have c := accepted_entry_installs_that_actual_job image.compiled image.tables pad Q.incoming Q.selected
    Q.synch Q.reserved Q.stored
  exact ⟨c.1,c.2.2⟩

def PublicRoot.rootAligned :
    image.tables.root=(rootPreparationFor Q.exterior).result :=
  image.tables.exactRoot.trans
    (congrArg Meter.result (one_root_cache_for_every_entry (W:=W) image.compiled Q.selected))

/-- Before the published row becomes resident, count the selected
lookup entry, actual duplicate views of the probe operand, creator,
creation/context words, and a prefix of the staged raw header.
This covers these serialized fields only, not the entire read stack. -/
def PublicRoot.wordCut (k : ℕ) : ℕ :=
  (entryBits Q.selected).length+
  2*(image.tables.requests.probes.read Q.selected.coord.1.2).result.val.length+
  Q.outerJob.identifier.bits.length+Q.outerJob.birth.bits.length+
  (Q.outerJob.ctx.magnitude.bits.length+Q.outerJob.ctx.codeWidth.bits.length+1)+
  (Q.outerJob.entry.result.bytes.take k).length

def PublicRoot.wordRoof : ℕ :=
  entryWidth kp tc tj tw+2*f.natDegree+KeyWidth kp tc tj+prec+tw+bw+1+
  Q.outerJob.entry.result.bytes.length

theorem actual_outer_publish_word_cut (k : ℕ) :
    Q.wordCut k≤Q.wordRoof := by
  unfold PublicRoot.wordCut PublicRoot.wordRoof
  have h : (Q.outerJob.entry.result.bytes.take k).length≤Q.outerJob.entry.result.bytes.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  rw [entry_bits_exact,(image.tables.requests.probes.read Q.selected.coord.1.2).result.property,
    Q.outerJob.identifier.size,Q.outerJob.birth.size,Q.outerJob.ctx.magnitude.size,
    Q.outerJob.ctx.codeWidth.size]
  omega

def PublicRoot.pageCut (pt : ExteriorPoint) : ℕ :=
  bitSize pageRequestBits ((exteriorPageRequests Q.exterior).result.take pt.requests)+
  bitSize atlasRowBits ((rootTable Q.exterior.chosenFields).take pt.nativeRows)+
  bitSize atlasRowBits (Q.outerJob.expected.pages.take pt.widenedRows)

def PublicRoot.pageRoof : ℕ :=
  let U := actualExteriorPageCap Q.exterior
  pagesCount (a m) (K m)*
    ((6*a m+6*a m+q+pageKeyWidth m)+(pageKeyWidth m+U)+(pageKeyWidth m+pad+U))

theorem actual_outer_publish_page_cut (pt : ExteriorPoint) :
    Q.pageCut pt≤Q.pageRoof :=
  real_external_atlas_cut_with_explicit_native_payload Q.exterior image.tables.root Q.rootAligned
    pad pt.requests pt.nativeRows pt.widenedRows

#print axioms actual_outer_bank_census
#print axioms actual_outer_publish_word_cut
#print axioms actual_outer_publish_page_cut
end
end J6R67.BootPeak
