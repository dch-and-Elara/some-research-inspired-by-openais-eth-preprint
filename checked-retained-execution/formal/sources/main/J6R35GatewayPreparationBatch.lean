import J6R35GatewayPreparationRender

/-! Actual shared scheduling, without assuming a pre-existing batch
of prepared results. One immutable root bundle is made; each supplied
legal request reads that bundle and builds the original bytes. -/
namespace J6R35GatewayPreparation
open scoped Classical Polynomial
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R15ModeCost
open J6R25PreparedSupply J6R17ModeTape J6R27OriginalGate J6R18ChildWrite
open J6R34RootAtlas J6R33PageIndexedBirth J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R21Ancestor
set_option maxHeartbeats 10500000
set_option maxRecDepth 2300
set_option linter.unusedSectionVars false

def collectPrepared {A B : Type*} (produce : A→Meter B) : List A→Meter (List B)
  | [] => ⟨[],2⟩
  | x::xs =>
    let r := produce x
    let rs := collectPrepared produce xs
    ⟨r.result::rs.result,r.steps+rs.steps+4⟩

theorem collect_prepared_exact {A B : Type*} (produce : A→Meter B) (xs : List A) :
    (collectPrepared produce xs).result=xs.map (fun a=>(produce a).result) ∧
      (collectPrepared produce xs).steps=(xs.map (fun a=>(produce a).steps)).sum+4*xs.length+2 := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    constructor
    · change (produce x).result::(collectPrepared produce xs).result=_
      rw [ih.1]
      rfl
    · change (produce x).steps+(collectPrepared produce xs).steps+4=_
      rw [ih.2,List.map_cons,List.sum_cons,List.length_cons]
      omega

section Root
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m))

structure CommonInputs (ell q rr cc dd : ℕ) where
  field : Meter (Frame f (J6SourcePrecision.printed m base))
  hf : f.Monic
  lit : LiteralPortFile T rr cc dd
  positive : 0<ell
  hq : 0<q
  qFits : 1<q
  copies : Word q
  receive : Word q
  copiesOK : copies.val=K m
  receiveOK : receive.val=J6SourcePrecision.printed m base
  copyFits : K m≤2^RootKey m
  code : ℕ
  codePos : 0<code
  codeOK : 1+(writeResidents m hq (oddAxis m) copies receive lit.raw).result.roster.modes.length<2^code

variable {G} {ell q rr cc dd : ℕ}
variable (C : CommonInputs (T:=T) (f:=f) (base:=base) ell q rr cc dd)

noncomputable def CommonInputs.make (C : CommonInputs (T:=T) (f:=f) (base:=base) ell q rr cc dd) :
    Meter (ActualRootPreparation G ell q) :=
  prepareSharedRoot G C.lit ell C.field C.hq C.copies C.receive

structure ExteriorQuery (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
    (J6R28GeneratedRootFrame.constantRootWord m))
    (ell edgew tc tj key prec tw bw : ℕ) where
  centre : J6Recovery.Addr m
  sample : Fin (literalDegree m native+1)
  group : Fin 64
  address : OccurrenceAddress tc tj
  centreOK : address.centre.val=index m centre
  sampleOK : address.sample.val=sample.val
  groupOK : address.group.val=group.val
  edgePos : 0<edgew
  edgeFit : (exteriorChild G ell centre sample group).edges<2^edgew
  issue : Meter (Word key)
  birth : Word prec
  birthOK : birth.val=J6SourcePrecision.printed m base
  context : CentreContext tw bw
  contextTime : context.center=(index m centre:ℤ)

variable {edgew tc tj key prec tw bw : ℕ}

structure LocalQuery (C : CommonInputs (T:=T) (f:=f) (base:=base) ell q rr cc dd)
    (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
      (J6R28GeneratedRootFrame.constantRootWord m)) (edgew tc tj key prec tw bw : ℕ) where
  req : ExteriorQuery G ell edgew tc tj key prec tw bw
  codeOK : req.context.codeWidth.val=C.code

def originalExterior (R : LocalQuery C G edgew tc tj key prec tw bw) :
    StableExterior G ell q rr cc dd edgew tc tj key prec tw bw where
  positive := C.positive
  field := C.field
  hf := C.hf
  source := C.lit
  centre := R.req.centre
  sample := R.req.sample
  group := R.req.group
  address := R.req.address
  timeOK := R.req.centreOK
  sampleOK := R.req.sampleOK
  groupOK := R.req.groupOK
  edgePos := R.req.edgePos
  edgeFit := R.req.edgeFit
  issue := R.req.issue
  birth := R.req.birth
  birthOK := R.req.birthOK
  hq := C.hq
  qFits := C.qFits
  copies := C.copies
  pre := C.receive
  copiesOK := C.copiesOK
  precOK := C.receiveOK
  copyFits := C.copyFits
  code := C.code
  codePos := C.codePos
  codeValid := C.codeOK
  context := R.req.context
  signedCentre := R.req.contextTime
  codeTruth := R.codeOK

abbrev SitePayload {p : ℕ} (F : Frame f p) (m ell q key : ℕ) :=
  DirRow key × Option (List (PageRow (a m) p ell q (pageKeyWidth m) F.words (oddAxis m)))

def renderOne (S : ActualRootPreparation G ell q) (R : LocalQuery C G edgew tc tj key prec tw bw) :
    Meter (SitePayload S.frame m ell q key) :=
  let X := originalExterior C R
  let h := headerUsingShared X S
  let a := atlasUsingShared X S
  ⟨(h.result,a.result),h.steps+a.steps+4⟩

noncomputable def fixedBatch (L : List (LocalQuery C G edgew tc tj key prec tw bw)) :
    Meter (List (SitePayload C.field.result m ell q key)) :=
  let root := CommonInputs.make (G:=G) C
  let jobs := collectPrepared (renderOne C root.result) L
  ⟨jobs.result,root.steps+jobs.steps+4⟩

theorem fixed_batch_actual_results (L : List (LocalQuery C G edgew tc tj key prec tw bw)) :
    let root := CommonInputs.make (G:=G) C
    let out := fixedBatch C L
    out.result=L.map (fun R => let X := originalExterior C R; (X.header.result,X.atlas.result)) ∧
    out.steps=root.steps+(L.map (fun R=>(renderOne C root.result R).steps)).sum+4*L.length+6 := by
  let root := CommonInputs.make (G:=G) C
  let f (R : LocalQuery C G edgew tc tj key prec tw bw) := renderOne C root.result R
  let J := collectPrepared f L
  obtain ⟨a,b⟩ := collect_prepared_exact f L
  constructor
  · change J.result=_
    rw [a]
    apply congrArg (fun fn=>L.map fn)
    funext R
    let X := originalExterior C R
    exact Prod.ext (shared_header_is_literal X).1.symm (shared_atlas_is_literal X).1.symm
  · change root.steps+J.steps+4=root.steps+(L.map (fun R=>(f R).steps)).sum+4*L.length+6
    change J.steps=(L.map (fun R=>(f R).steps)).sum+4*L.length+2 at b
    rw [b]
    omega

end Root

#print axioms collect_prepared_exact
#print axioms fixed_batch_actual_results
end J6R35GatewayPreparation
