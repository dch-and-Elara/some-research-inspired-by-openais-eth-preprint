import J6R105OuterPublication
import J6R34RootAtlasFee

namespace J6R106OuterPublication
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R34RootAtlas J6R35GatewayPreparation
open J6R33PageIndexedBirth J6R32ChildResidentTransfer J6R32RootGeneratedRegistryInputs
open J6R54PublicFamily J6R57PublicRequest J6R75OuterTime J6R105OuterPublication
open P11FullPacking J6Mesh J6OrientedHost J6R24LegalLayout J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R31RootResidentTables

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4700
set_option maxHeartbeats 18000000

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]}
variable {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw kp : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem ready_page_compilation_does_not_pay_for_shared_input_twice
    (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
    (S : ActualRootPreparation G ell q) (aligned : S=(rootPreparationFor X).result) :
    (readyAtlas X S aligned).steps+X.field.steps+(buildRootBitBank G ell).steps+
      (writeResidents m X.hq (oddAxis m) X.copies X.pre X.source.raw).steps+4=X.atlas.steps := by
  subst S
  have same : (readyAtlas X (rootPreparationFor X).result rfl).steps=
      (atlasUsingShared X (rootPreparationFor X).result).steps := rfl
  rw [same, (shared_atlas_is_literal X).2]


variable {W : Widths m native tc tj tw edgew}
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+0))

theorem actual_cached_exterior_publication_explicit
    (pad : ℕ) (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (r : Entry D.mark m native tc tj tw) :
    let X := (entrySource (W:=W) D r).result
    let J := cachedExteriorJob D S pad r
    let E := headerUsingShared X S.root
    let aligned := S.exactRoot.trans (congrArg Meter.result (one_root_cache_for_every_entry (W:=W) D r))
    publishFee B J.entry J.offset J.built=
      E.steps+(readyAtlas X S.root aligned).steps+
      pagesCount (a m) (K m)*(wideningFee (pageKeyWidth m) pad+7)+6+shapeFrameFee prec+
      headerBill (KeyWidth kp tc tj) prec tw bw (externalAddrWidth tc tj 0)
        B.headers.length B.records.length (storedHeaderBits B.headers) E.result.bytes.length := by
  let X := (entrySource (W:=W) D r).result
  let aligned := S.exactRoot.trans (congrArg Meter.result (one_root_cache_for_every_entry (W:=W) D r))
  exact actual_prepared_publication_counts_each_page_and_header X S.root aligned pad B

#print axioms ready_page_compilation_does_not_pay_for_shared_input_twice
#print axioms actual_cached_exterior_publication_explicit
end
end J6R106OuterPublication
