import J6R34RootAtlasAll
import J6R34RootAtlasSeed
import J6R32RootGeneratedRegistryInputsRoot

/-! The concrete stable outer source: generate the actual positive
nonzero probe tape, root half-port file and complete root Page atlas
before its one real exterior call. The same data enter the publisher
checked by its refetched creation word. -/
namespace J6R34RootAtlas
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R12
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R30ProducedGateRegistry
open J6R32RootGeneratedRegistryInputs J6R33PageIndexedBirth
open J6R15ModeCost J6R27OriginalGate J6R17ModeTape J6R18ChildWrite J6R21Ancestor
open J6R14ZeroMode J6R27PrescribedProbe J6R26StablePreparedRoot J6R16ModeCost J6R20Ancestor
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R26DescriptorTree J6R25PreparedSupply
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R12Blueprint J6R11Blueprint J6R12Repack J6R11Repack J6R10Repack
set_option maxHeartbeats 21000000
set_option maxRecDepth 2700

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m))

noncomputable abbrev sampleCount (f : ℤ[X]) (ell m base n native : ℕ) {V : Type} [Fintype V] (T : Plant V m n) :=
  externalProbeDegree (physicalSize m native)
    (physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m))+1

structure StableExterior
    (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (J6R28GeneratedRootFrame.constantRootWord m))
    (ell q r c d edgew tc tj key prec tw bw : ℕ) where
  positive : 0<ell
  field : Meter (Frame f (J6SourcePrecision.printed m base))
  hf : f.Monic
  source : LiteralPortFile T r c d
  centre : J6Recovery.Addr m
  sample : Fin (sampleCount f ell m base n native T)
  group : Fin 64
  address : OccurrenceAddress tc tj
  timeOK : address.centre.val=index m centre
  sampleOK : address.sample.val=sample.val
  groupOK : address.group.val=group.val
  edgePos : 0<edgew
  edgeFit : (exteriorChild G ell centre sample group).edges<2^edgew
  issue : Meter (Word key)
  birth : Word prec
  birthOK : birth.val=J6SourcePrecision.printed m base
  hq : 0<q
  qFits : 1<q
  copies : Word q
  pre : Word q
  copiesOK : copies.val=K m
  precOK : pre.val=J6SourcePrecision.printed m base
  copyFits : K m≤2^RootKey m
  code : ℕ
  codePos : 0<code
  codeValid : 1+(writeResidents m hq (oddAxis m) copies pre source.raw).result.roster.modes.length<2^code
  context : CentreContext tw bw
  signedCentre : context.center=(index m centre:ℤ)
  codeTruth : context.codeWidth.val=code

variable {ell q r c d edgew tc tj key prec tw bw : ℕ}
variable {G}
variable (X : StableExterior G ell q r c d edgew tc tj key prec tw bw)

abbrev StableExterior.frame : FrameShape f prec :=
  exteriorShape (q:=q) X.field.result (oddAxis m) X.birth X.birthOK

noncomputable def StableExterior.header : Meter (DirRow key) :=
  let P := makeTypedRootParent G X.source ell X.centre
  padCost (makeOccurrence (b:=edgew) X.address X.birth (word (q:=1) 0) P.result.raw X.issue) P.steps

noncomputable def StableExterior.atlas :
    Meter (Option (PageRows X.frame ell (pageKeyWidth m))) :=
  let B := buildRootBitBank G ell
  let F := buildRootAtlas X.field.result X.hf B.result m X.hq (oddAxis m) X.qFits.le
    X.copies X.pre X.source.raw X.group X.sample X.code X.positive
  padCost F (X.field.steps+B.steps+4)

theorem stable_exterior_header
    : X.header.result.id=X.issue.result ∧
      loadAt prec (externalAddrWidth tc tj 0) X.header.result.bytes=
        ⟨some X.birth,headerReadFee prec (externalAddrWidth tc tj 0)⟩ ∧
      X.birth.val=(exteriorChild G ell X.centre X.sample X.group).prec := by
  let P := makeTypedRootParent G X.source ell X.centre
  have field : (X.address.centre.val:ℤ)=(G.centre ell X.centre).val := by
    rw [X.timeOK,(odd_site_matches_geometry G ell X.centre).2.2.1]
  have precision : X.birth.val=registerPrecision (rootParams f ell m native)
      (physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m))
      (G.centre ell X.centre) := X.birthOK.trans (G.precision ell X.centre).symm
  obtain ⟨owner,_,tag,p⟩ := true_occurrence_header (G.selector ell) (G.ready ell) (G.centre ell X.centre)
    P.result (rootPreset G ell) X.sample X.group X.address field X.sampleOK X.groupOK X.issue
    X.birth precision (word (q:=1) 0) (by rfl) (by decide) (show (1:ℕ)<2 by decide) X.edgePos X.edgeFit
  exact ⟨owner,tag,p⟩

theorem stable_exterior_atlas :
    ∃ fields : Page (a m) (K m) (Fin 64)→OriginFields (a m) (J6SourcePrecision.printed m base)
        ell q X.field.result.words (oddAxis m),
      X.atlas.result=some (rootTable fields) ∧
      (∀ k,(locate (residentPageKey m k) (rootTable fields)).result=some (fields k)) ∧
      (∀ k, J6R22Active.boxTransport X.field.result.exactMod
        (A1R10.uvRead X.field.result.hp X.field.result.words ell (fields k).probe)=
        prescribedNode (rootPreset G ell) (J6SourcePrecision.printed m base) ell X.sample) := by
  obtain ⟨fields,ok,_,hits,laws,_⟩ := actual_prescribed_root_atlas X.source X.field.result X.hf X.positive
    (buildRootBitBank G ell).result X.sample X.hq (oddAxis m) X.qFits X.copies X.pre X.copiesOK X.precOK
    X.group X.code X.codePos X.codeValid X.copyFits
  refine ⟨fields,ok,hits,fun k=>?_⟩
  obtain ⟨_,_,probe,_⟩ := laws k
  exact probe

noncomputable def StableExterior.chosenFields :=
  Classical.choose (stable_exterior_atlas X)

noncomputable def StableExterior.seed (pad : ℕ) : PageJob f ell key prec tw bw (pageKeyWidth m+pad) :=
  rootJob X.frame X.header (externalAddrWidth tc tj 0) X.context (stable_exterior_header X).2.1
    pad X.atlas (rootTable X.chosenFields) (Classical.choose_spec (stable_exterior_atlas X)).1

theorem true_exterior_seed_lookup (pad : ℕ) (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (sync : B.synced) (fresh : ∀ row∈B.headers,row.id≠X.issue.result)
    (k : Page (a m) (K m) (Fin 64)) :
    let j := X.seed pad
    let out := j.install B
    out.result.2=true ∧ IsLive j out.result.1 ∧
      j.identifier=X.issue.result ∧
      (locate (widened pad (residentPageKey m k)).result j.immutable.payload.payload.pages).result=
        some (X.chosenFields k) ∧ j.immutable.payload.stamp.created.val=(exteriorChild G ell X.centre X.sample X.group).prec ∧
      J6R22Active.boxTransport X.field.result.exactMod
        (A1R10.uvRead X.field.result.hp X.field.result.words ell (X.chosenFields k).probe)=
        prescribedNode (rootPreset G ell) (J6SourcePrecision.printed m base) ell X.sample := by
  let j := X.seed pad
  have header := stable_exterior_header X
  have needed : ∀ row∈B.headers,row.id≠X.header.result.id := by rw [header.1]; exact fresh
  have wit := Classical.choose_spec (stable_exterior_atlas X)
  obtain ⟨valid,live,hit,_,_⟩ := actual_root_seed_paid X.frame X.header (externalAddrWidth tc tj 0)
    X.context header.2.1 pad X.atlas (rootTable X.chosenFields) wit.1 B sync needed
    (residentPageKey m k) (X.chosenFields k) (wit.2.1 k)
  exact ⟨valid,live,header.1,hit,header.2.2,wit.2.2 k⟩

#print axioms stable_exterior_header
#print axioms stable_exterior_atlas
#print axioms true_exterior_seed_lookup
end J6R34RootAtlas
