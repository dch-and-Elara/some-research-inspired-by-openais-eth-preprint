import J6R34RootAtlasStable

/-! Exact outer publication overhead and bounds for the actually
generated root bit tape, shared residents, and compiled Page atlas. -/
namespace J6R34RootAtlas
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R12
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R30ProducedGateRegistry
open J6R32RootGeneratedRegistryInputs J6R33PageIndexedBirth
open J6R15ModeCost J6R27OriginalGate J6R17ModeTape J6R18ChildWrite J6R21Ancestor
open J6R14ZeroMode J6R27PrescribedProbe J6R26StablePreparedRoot J6R16ModeCost
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic
set_option maxHeartbeats 9500000

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q r c d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q r c d edgew tc tj key prec tw bw)

theorem stable_atlas_preparation_bound :
    let N := (writeResidents m X.hq (oddAxis m) X.copies X.pre X.source.raw).result.roster.modes.length
    let p := J6SourcePrecision.printed m base
    let D := sampleCount f ell m base n native T
    X.atlas.steps≤X.field.steps+(positiveTapeFee f.natDegree D+3)+4+
      (residentsFee m q 0 p r c d+D*(f.natDegree+2)+3*X.code+12+
        requestsFee (a m) (RootKey m) q (K m)+
        pagesCount (a m) (K m)*(framePayloadFee p ell X.field.result.words.length (a m) 0 q X.code
          (pageKeyWidth m) (M m) N (J6Mesh.D m*K m)+onePageFee (pageKeyWidth m)+5)+6) := by
  let O := buildRootBitBank G ell
  let A := buildRootAtlas X.field.result X.hf O.result m X.hq (oddAxis m) X.qFits.le
    X.copies X.pre X.source.raw X.group X.sample X.code X.positive
  let n0 := sampleCount f ell m base n native T
  obtain ⟨_,_,_,_,_,bound⟩ := actual_prescribed_root_atlas X.source X.field.result X.hf X.positive
    O.result X.sample X.hq (oddAxis m) X.qFits X.copies X.pre X.copiesOK X.precOK X.group X.code
    X.codePos X.codeValid X.copyFits
  have root := build_root_probe_receipt G ell
  have exactO : O.steps=positiveTapeFee f.natDegree n0+3 := root.1
  have exactRead : (O.result.read X.sample).steps≤n0*(f.natDegree+2) := (root.2 X.sample).2
  have fee : A.steps≤residentsFee m q 0 (J6SourcePrecision.printed m base) r c d+
      (O.result.read X.sample).steps+3*X.code+12+
      requestsFee (a m) (RootKey m) q (K m)+
        pagesCount (a m) (K m)*(framePayloadFee (J6SourcePrecision.printed m base) ell
         X.field.result.words.length (a m) 0 q X.code (pageKeyWidth m) (M m)
         (writeResidents m X.hq (oddAxis m) X.copies X.pre X.source.raw).result.roster.modes.length
         (J6Mesh.D m*K m)+onePageFee (pageKeyWidth m)+5)+6 := bound
  change A.steps+(X.field.steps+O.steps+4)≤
    X.field.steps+(positiveTapeFee f.natDegree n0+3)+4+
      (residentsFee m q 0 (J6SourcePrecision.printed m base) r c d+n0*(f.natDegree+2)+3*X.code+12+
        requestsFee (a m) (RootKey m) q (K m)+
        pagesCount (a m) (K m)*(framePayloadFee (J6SourcePrecision.printed m base) ell
          X.field.result.words.length (a m) 0 q X.code (pageKeyWidth m) (M m)
          (writeResidents m X.hq (oddAxis m) X.copies X.pre X.source.raw).result.roster.modes.length
          (J6Mesh.D m*K m)+onePageFee (pageKeyWidth m)+5)+6)
  rw [exactO]
  omega

theorem stable_seed_bill (pad : ℕ) (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (sync : B.synced) (fresh : ∀ row∈B.headers,row.id≠X.issue.result)
    (k : Page (a m) (K m) (Fin 64)) :
    let job := X.seed pad
    (job.install B).steps=publishFee B X.header (externalAddrWidth tc tj 0)
      ⟨some ⟨X.frame,(rootTable X.chosenFields).map (mappedRow pad)⟩,
        X.atlas.steps+(2+(rootTable X.chosenFields).length*(wideningFee (pageKeyWidth m) pad+7))+4+
          shapeFrameFee prec⟩ := by
  have header := stable_exterior_header X
  have needed : ∀ row∈B.headers,row.id≠X.header.result.id := by rw [header.1]; exact fresh
  have wit := Classical.choose_spec (stable_exterior_atlas X)
  exact (actual_root_seed_paid X.frame X.header (externalAddrWidth tc tj 0)
    X.context header.2.1 pad X.atlas (rootTable X.chosenFields) wit.1 B sync needed
    (residentPageKey m k) (X.chosenFields k) (wit.2.1 k)).2.2.2.2

#print axioms stable_atlas_preparation_bound
#print axioms stable_seed_bill
end J6R34RootAtlas
