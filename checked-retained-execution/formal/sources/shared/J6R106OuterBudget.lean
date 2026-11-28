import J6R106OuterGeometry
import J6R34RootAtlasFee

namespace J6R106OuterBudget
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R34RootAtlas J6R35GatewayPreparation
open J6R33PageIndexedBirth J6R32ChildResidentTransfer J6R32RootGeneratedRegistryInputs
open J6R54PublicFamily J6R57PublicRequest J6R75OuterTime
open J6R105OuterPublication J6R106OuterPublication J6R106OuterHeader J6R106OuterGeometry
open J6R30GeneratedRootLayout P11FullPacking J6Mesh J6OrientedHost J6R24LegalLayout J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R31RootResidentTables J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5100
set_option maxHeartbeats 22000000

def cachedAtlasClock (m q p rr cc dd ell e samples words code modeRows : ℕ) : ℕ :=
  residentsFee m q 0 p rr cc dd+samples*(e+2)+3*code+12+
    requestsFee (a m) (RootKey m) q (K m)+
    pagesCount (a m) (K m)*(framePayloadFee p ell words (a m) 0 q code
      (pageKeyWidth m) (M m) modeRows (J6Mesh.D m*K m)+onePageFee (pageKeyWidth m)+5)+6

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]}
variable {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw kp : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem real_cached_atlas_clock
    (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
    (S : ActualRootPreparation G ell q) (aligned : S=(rootPreparationFor X).result) :
    (readyAtlas X S aligned).steps≤cachedAtlasClock m q (J6SourcePrecision.printed m base)
      rr cc dd ell f.natDegree (sampleCount f ell m base n native T) X.field.result.words.length
      X.code S.resident.roster.modes.length := by
  have h : (readyAtlas X S aligned).steps+X.field.steps+(buildRootBitBank G ell).steps+
      (writeResidents m X.hq (oddAxis m) X.copies X.pre X.source.raw).steps+4=X.atlas.steps :=
    ready_page_compilation_does_not_pay_for_shared_input_twice X S aligned
  have same : S.resident=(writeResidents m X.hq (oddAxis m) X.copies X.pre X.source.raw).result := by
    subst S
    rfl
  have tape : (buildRootBitBank G ell).steps=
      positiveTapeFee f.natDegree (sampleCount f ell m base n native T)+3 :=
    (build_root_probe_receipt G ell).1
  have roof := stable_atlas_preparation_bound X
  change X.atlas.steps≤X.field.steps+(positiveTapeFee f.natDegree
      (sampleCount f ell m base n native T)+3)+4+
    cachedAtlasClock m q (J6SourcePrecision.printed m base) rr cc dd ell f.natDegree
      (sampleCount f ell m base n native T) X.field.result.words.length X.code
      (writeResidents m X.hq (oddAxis m) X.copies X.pre X.source.raw).result.roster.modes.length at roof
  rw [←h, tape,←same] at roof
  omega

variable {W : Widths m native tc tj tw edgew}
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)

def selectedPublicationClock (pad : ℕ)
    (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) : ℕ :=
  exteriorHeaderOps m tc tj prec edgew (KeyWidth kp tc tj)+
    cachedAtlasClock m q (J6SourcePrecision.printed m base) rr cc dd ell f.natDegree
      (sampleCount f ell m base n native T) D.frame.words.length D.code S.root.resident.roster.modes.length+
    pagesCount (a m) (K m)*(wideningFee (pageKeyWidth m) pad+7)+6+shapeFrameFee prec+
    headerBill (KeyWidth kp tc tj) prec tw bw (externalAddrWidth tc tj 0)
      B.headers.length B.records.length (storedHeaderBits B.headers) (exteriorHeaderBits m tc tj prec edgew)

theorem compiled_publication_obeys_one_real_bank_clock (pad : ℕ)
    (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (r : Entry D.mark m native tc tj tw) :
    let job := cachedExteriorJob D S pad r
    publishFee B job.entry job.offset job.built≤selectedPublicationClock D S pad B := by
  let X := (entrySource (W:=W) D r).result
  let aligned := S.exactRoot.trans (congrArg Meter.result (one_root_cache_for_every_entry (W:=W) D r))
  have issue : X.issue.steps≤6*KeyWidth kp tc tj+10 := by
    change (issueExterior D.mark (realAddress r.head.data r.coord.2).result).steps≤_
    exact (issued_exterior_exact _ _).2.le
  have hb := shared_header_caps_use_actual_closed_parent X S.root aligned issue
  dsimp only at hb
  have a0 := real_cached_atlas_clock X S.root aligned
  have a1 : (readyAtlas X S.root aligned).steps≤
      cachedAtlasClock m q (J6SourcePrecision.printed m base) rr cc dd ell f.natDegree
        (sampleCount f ell m base n native T) D.frame.words.length D.code S.root.resident.roster.modes.length :=
    a0
  have fee := actual_cached_exterior_publication_explicit D S pad B r
  dsimp only at fee ⊢
  rw [fee]
  unfold selectedPublicationClock headerBill
  have hbytes := hb.1
  have hops := hb.2
  gcongr

#print axioms real_cached_atlas_clock
#print axioms compiled_publication_obeys_one_real_bank_clock
end
end J6R106OuterBudget
