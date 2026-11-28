import J6R36SharedGatewayRun
import J6R35GatewayPreparationBatch

/-! Every legal address uses one and the same produced root bundle,
but keeps its own explicit, actual legal downstream job. Complete
the source slot with the real product of all 64 group replies. -/
namespace J6R36SharedGateway
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R12
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R34RootAtlas J6R35GatewayPreparation J6R34OfficialGateway J6R33OriginalJ6
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R22Active
open J6R32RootGeneratedRegistryInputs J6R31RootResidentTables J6R19Retained
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R30ProducedGateRegistry
set_option maxHeartbeats 14500000
set_option maxRecDepth 2550
set_option linter.unusedSectionVars false

section Source
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m))
variable {ell q rr cc dd edgew tc tj key prec tw bw : ℕ}
variable (C : CommonInputs (T:=T) (f:=f) (base:=base) ell q rr cc dd)
variable (pad : ℕ)

structure SharedOccurrence (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) where
  query : LocalQuery C G edgew tc tj key prec tw bw
  actual : AtlasJob (originalExterior C query) pad
  centre : query.req.centre=i
  probe : query.req.sample=j
  group : query.req.group=g

abbrev SharedRequests (edgew tc tj key prec tw bw : ℕ) :=
  ∀ i j g, SharedOccurrence (edgew:=edgew) (tc:=tc) (tj:=tj)
    (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) G C pad i j g

variable {G C pad}
variable {i : J6Recovery.Addr m} {j : Fin (literalDegree m native+1)} {g : Fin 64}
variable (A : SharedOccurrence (edgew:=edgew) (tc:=tc) (tj:=tj)
  (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) G C pad i j g)

abbrev SharedOccurrence.exterior := originalExterior C A.query

def toFreshRequest :
    ActualRequest (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd) (edgew:=edgew) (tc:=tc) (tj:=tj)
      (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) G pad i j g :=
  ⟨A.exterior,A.actual,A.centre,A.probe,A.group⟩

variable (S : ActualRootPreparation G ell q)
variable (held : S=(CommonInputs.make (G:=G) C).result)

include held in
theorem has_actual_root_for_occurrence : S=(rootPreparationFor A.exterior).result := held

noncomputable def sharedReceipt [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    GroupReceipt (ell:=ell) G C.hf i j g :=
  transportRequest G C.hf A.centre A.probe A.group
    (cachedGroupReceipt A.exterior S (has_actual_root_for_occurrence A S held) pad A.actual)

theorem shared_receipt_from_actual_paid_run [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    (sharedReceipt A S held).run.steps=
      (runCached A.exterior S (has_actual_root_for_occurrence A S held) pad A.actual).steps := by
  exact address_cast_keeps_steps (ell:=ell) G C.hf A.centre A.probe A.group
    (cachedGroupReceipt A.exterior S (has_actual_root_for_occurrence A S held) pad A.actual)

include held in
theorem same_root_data_each_request :
    S.frame=A.exterior.field.result ∧
    (S.probes.read j).result.val=encodeBits f.natDegree (j.val+1) ∧
    S.parents=(makeTypedRootParent G A.exterior.source ell A.exterior.centre).result.raw := by
  have H := cached_keeps_probe_frame_and_halves A.exterior S (has_actual_root_for_occurrence A S held)
  exact ⟨H.1,H.2.1 j,H.2.2⟩

section All
variable (supply : SharedRequests G C pad edgew tc tj key prec tw bw)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

noncomputable def cachedSlot (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) :
    Meter (Block (SiteFrame G ell C.field.result i) ell) :=
  completedGroups G C.hf C.field.result C.positive i j (fun g=>sharedReceipt (supply i j g) S held)

noncomputable def cachedOracle : CompletedOracle G ell C.field.result C.hf :=
  completedOracle G C.hf C.field.result C.positive (fun i j g=>sharedReceipt (supply i j g) S held)

noncomputable def freshlyBuiltOracle : CompletedOracle G ell C.field.result C.hf :=
  sourceAtlasOracle G pad C.field.result C.hf C.positive (fun i j g=>toFreshRequest (supply i j g))

theorem cached_all64_reply_equals_fresh
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (raw : List Bool)
    (ok : raw=(S.probes.read j).result.val) :
    let cached := cachedOracle S held supply
    let fresh := freshlyBuiltOracle supply
    cached.reply i j raw=(cachedSlot S held supply i j).result ∧
    cached.reply i j raw=fresh.reply i j raw ∧
    (SiteFrame G ell C.field.result i).decode (cached.reply i j raw)=
      fallbackTable (G.selector ell) (G.ready ell) (G.centre ell i) C.hf (rootPreset G ell) j := by
  let O := cachedOracle S held supply
  let F := freshlyBuiltOracle supply
  have legal := ok.trans (S.probes.consistent j)
  have v := gateway_reply_exact G C.hf C.field.result C.positive
    (fun i j g=>sharedReceipt (supply i j g) S held) i j raw legal
  have e := O.correct i j raw legal
  have f0 := F.correct i j raw legal
  exact ⟨v.1,frame_words_injective C.hf (SiteFrame G ell C.field.result i) (e.trans f0.symm),e⟩

noncomputable def siteReceipt (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
    Meter (Block (SiteFrame G ell C.field.result i) ell) :=
  groupOnSite G C.hf C.field.result i j g (sharedReceipt (supply i j g) S held)

/-- Equality of the actual 64 input blocks to the same ring product,
not simply equality of their decoded product. Each group is associated
to the same fixed typed child as in the independently built gateway. -/
theorem cached_tuple_is_literal
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) :
    (fun g=>(siteReceipt S held supply i j g).result)=
      (fun g=>(groupOnSite G C.hf C.field.result i j g
        (requestReceipt G pad C.hf (toFreshRequest (supply i j g)))).result) := by
  funext g
  let new := sharedReceipt (supply i j g) S held
  let old := requestReceipt G pad C.hf (toFreshRequest (supply i j g))
  exact frame_words_injective C.hf (SiteFrame G ell C.field.result i)
    ((group_on_site_exact G C.hf C.field.result i j g new).1.trans
      (group_on_site_exact G C.hf C.field.result i j g old).1.symm)

theorem cached_product_exact_fee
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) :
    let E := SiteFrame G ell C.field.result i
    let one := siteReceipt S held supply i j
    let onlyProduct := foldM E.hp E.sizePos C.positive (fun g=>bare (one g)) (groupOrder 64)
    (cachedSlot S held supply i j).result=onlyProduct.result ∧
    (cachedSlot S held supply i j).steps=onlyProduct.steps+bill one (groupOrder 64) := by
  let E := SiteFrame G ell C.field.result i
  let one := siteReceipt S held supply i j
  have h := product_delta E.hp E.sizePos C.positive one (fun g=>bare (one g))
    (fun g=>(one g).steps) (groupOrder 64) (fun g _=>Delta.bare (one g))
  exact ⟨h.value,h.fee⟩

theorem one_group_run_and_copy_fee
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
    let E := SiteFrame G ell C.field.result i
    let R := sharedReceipt (supply i j g) S held
    let Q : Meter (Block E ell) :=
      resizeUV ((R.frame.natDegree C.hf).trans (E.natDegree C.hf).symm) R.run.result
    let a := supply i j g
    (siteReceipt S held supply i j g).steps=
      (runCached a.exterior S (has_actual_root_for_occurrence a S held) pad a.actual).steps+Q.steps+4 := by
  let E := SiteFrame G ell C.field.result i
  let R := sharedReceipt (supply i j g) S held
  let Q : Meter (Block E ell) :=
    resizeUV ((R.frame.natDegree C.hf).trans (E.natDegree C.hf).symm) R.run.result
  let a := supply i j g
  change R.run.steps+Q.steps+4=(runCached a.exterior S (has_actual_root_for_occurrence a S held) pad a.actual).steps+Q.steps+4
  rw [show R.run.steps = _ from shared_receipt_from_actual_paid_run a S held]

end All
end Source

#print axioms shared_receipt_from_actual_paid_run
#print axioms same_root_data_each_request
#print axioms cached_all64_reply_equals_fresh
#print axioms cached_tuple_is_literal
#print axioms cached_product_exact_fee
#print axioms one_group_run_and_copy_fee
end J6R36SharedGateway
