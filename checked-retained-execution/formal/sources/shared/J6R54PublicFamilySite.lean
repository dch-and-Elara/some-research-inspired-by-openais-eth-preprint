import J6R54PublicFamilyCommon
import J6R54PublicFamilyWords

/-! A public site is built from one captured common chart and the actual
paid head for (centre, sample); only its group address is emitted here.
The archived header/atlas remains the consumer, not a new row model. -/
namespace J6R54PublicFamily
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6Mesh J6OrientedHost J6R15ModeCost
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R52FreshExterior
open J6R14ZeroMode J6R27PrescribedProbe J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R12Blueprint J6ActiveRun J6R30ProducedGateRegistry
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
set_option maxRecDepth 3200
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

def prepareShared (I : SharedInputs G ell q rr cc dd prec kp bw) :
    Meter (Compiled G ell q rr cc dd prec kp bw) :=
  prepShared I (emitOrdinal bw I.code)
    (emitted_ordinal_exact bw I.code I.codeWordWidthPositive I.codeFit).1

theorem prepare_shared_exact_cost (I : SharedInputs G ell q rr cc dd prec kp bw) :
    (prepareShared I).steps=I.literal.steps+I.field.steps+
      (computeExteriorRegisters m prec I.baseWord).steps+ordinalFee bw I.code+11 := by
  have h := shared_uses_compiled_data I (emitOrdinal bw I.code)
    (emitted_ordinal_exact bw I.code I.codeWordWidthPositive I.codeFit).1
  change (prepShared I _ _).steps=_
  rw [h.2.2.2.2,(emitted_ordinal_exact bw I.code I.codeWordWidthPositive I.codeFit).2]

structure Widths (m native tc tj tw edgew : ℕ) where
  centrePos : 0<tc
  samplePos : 0<tj
  centreFit : 2*m+1<2^tc
  sampleFit : literalDegree m native<2^tj
  magnitudeFit : 2*m+1<2^tw
  edgePos : 0<edgew
  edgeFit : 2*physicalSize m native<2^edgew

structure ExactHead (m native tc tj tw : ℕ) (i : J6Recovery.Addr m)
    (j : Fin (literalDegree m native+1)) where
  data : QueryHead tc tj tw
  centreOK : data.centre.val=index m i
  sampleOK : data.sample.val=j.val
  magnitudeOK : data.magnitude.val=index m i

variable (W : Widths m native tc tj tw edgew)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))

include W in
theorem uniform_centre_sample_fits :
    index m i<2^tc ∧ j.val<2^tj ∧ index m i<2^tw := by
  have C : index m i≤2*m+1 := by
    have P := i.isLt
    unfold index
    omega
  have J : j.val≤literalDegree m native := Nat.le_of_lt_succ j.isLt
  exact ⟨C.trans_lt W.centreFit,J.trans_lt W.sampleFit,C.trans_lt W.magnitudeFit⟩

include W in
def prepareHead : Meter (ExactHead m native tc tj tw i j) :=
  let F := uniform_centre_sample_fits W i j
  let R := emitQueryHead tc tj tw (index m i) j.val
  let E := emitted_query_head_exact W.centrePos W.samplePos F.1 F.2.1 F.2.2
  ⟨⟨R.result,E.1,E.2.1,E.2.2.1⟩,R.steps⟩

include W in
theorem query_head_exact_fee :
    (prepareHead W i j).steps=
      ordinalFee tc (index m i)+ordinalFee tj j.val+(2*tc+4*tw+5)+6 :=
  let F := uniform_centre_sample_fits W i j
  (emitted_query_head_exact W.centrePos W.samplePos F.1 F.2.1 F.2.2).2.2.2

variable (G) (ell) (g : Fin 64)

theorem exterior_edge_count_le :
    (exteriorChild G ell i j g).edges≤2*physicalSize m native := by
  let child := exteriorChild G ell i j g
  let z := prescribedNode (rootPreset G ell) child.prec ell j
  have st : Stable (physicalSize m native) 2 child :=
    zeroChild_stable (G.selector ell) (G.ready ell) (G.centre ell i) (G.stable ell) z g
  have p : 1≤(8:ℕ)^child.depth := Nat.succ_le_of_lt (by positivity)
  have le := Nat.mul_le_mul_right child.edges p
  rw [Nat.one_mul] at le
  exact le.trans st.sizeByDepth

variable {G ell i j} (C : Compiled G ell q rr cc dd prec kp bw)
variable (H : ExactHead m native tc tj tw i j)

def siteFromHead :
    Meter (StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw) :=
  let A := realAddress H.data g
  let e := real_address_exact H.data g
  let S : SetupOutsideWords G ell edgew tc tj (KeyWidth kp tc tj) tw bw :=
    { positive := C.positive
      field := ⟨C.frame,0⟩
      hf := C.hf
      centre := i
      sample := j
      group := g
      address := A.result
      timeOK := (congrArg Word.val e.1).trans H.centreOK
      sampleOK := (congrArg Word.val e.2.1).trans H.sampleOK
      groupOK := e.2.2.1
      edgePos := W.edgePos
      edgeFit := (exterior_edge_count_le (G:=G) (ell:=ell) i j g).trans_lt W.edgeFit
      issue := issueExterior C.mark A.result
      code := C.code
      codeBound := C.codeBound
      context := signedContext H.data C.codeTape
      signedCentre := congrArg (fun u : ℕ => (u:ℤ)) H.magnitudeOK
      codeTruth := C.codeTruth }
  let X := setupFromProducedWords S C.regs C.copiesOK C.preOK C.birthOK
  ⟨attachLiteralWithPublicWidth X C.literal C.codeBound,A.steps+5⟩

theorem site_keeps_shared_payload :
    let S := siteFromHead W g C H
    S.result.source=C.literal ∧ S.result.field=⟨C.frame,0⟩ ∧
      S.result.centre=i ∧ S.result.sample.val=j.val ∧ S.result.group=g ∧
      S.result.copies=C.regs.copies ∧ S.result.pre=C.regs.pre ∧ S.result.birth=C.regs.birth ∧
      S.result.context.codeWidth=C.codeTape ∧
      S.result.issue=issueExterior C.mark (realAddress H.data g).result :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem site_exact_local_fee :
    (siteFromHead W g C H).steps=ordinalFee 6 g.val+8 := by
  change (realAddress H.data g).steps+5=_
  rw [(real_address_exact H.data g).2.2.2]

#print axioms prepare_shared_exact_cost
#print axioms uniform_centre_sample_fits
#print axioms query_head_exact_fee
#print axioms exterior_edge_count_le
#print axioms siteFromHead
#print axioms site_keeps_shared_payload
#print axioms site_exact_local_fee
end
end J6R54PublicFamily

