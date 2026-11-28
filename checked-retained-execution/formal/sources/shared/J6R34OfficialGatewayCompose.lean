import J6R34OfficialGatewayAtlas

/-! Assemble one oracle on the unchanged generated chart. The caller
must provide a real, routable paged execution for all 64 groups of
each legal request. That is an implementation premise, not a premise
of the source's separate polynomial-query reduction. -/
namespace J6R34OfficialGateway
open scoped Polynomial Classical
open Polynomial Std.Sat AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R34RootAtlas J6R33OriginalJ6 J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode
open J6R28GeneratedRootFrame J6R29BinaryFieldSearch
open J6R32RootGeneratedRegistryInputs J6R31RootResidentTables J6R30ProducedGateRegistry J6R21Ancestor
set_option maxHeartbeats 15000000
set_option maxRecDepth 2500
set_option linter.unusedSectionVars false

section Chart
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m))
variable {ell q rr cc dd edgew tc tj key prec tw bw : ℕ}
variable (pad : ℕ)

structure ActualRequest (i : J6Recovery.Addr m)
    (j : Fin (literalDegree m native+1)) (g : Fin 64) where
  exterior : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw
  actual : AtlasJob exterior pad
  centre : exterior.centre=i
  probe : exterior.sample=j
  group : exterior.group=g

def transportRequest (hf : f.Monic)
    {i₀ i : J6Recovery.Addr m} {j₀ j : Fin (literalDegree m native+1)} {g₀ g : Fin 64}
    (hi : i₀=i) (hj : j₀=j) (hg : g₀=g)
    (R : GroupReceipt (ell:=ell) G hf i₀ j₀ g₀) : GroupReceipt (ell:=ell) G hf i j g :=
  hi ▸ hj ▸ hg ▸ R

noncomputable def requestReceipt [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hf : f.Monic) {i : J6Recovery.Addr m} {j : Fin (literalDegree m native+1)} {g : Fin 64}
    (A : ActualRequest (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
      (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) G pad i j g) :
    GroupReceipt (ell:=ell) G hf i j g :=
  transportRequest G hf A.centre A.probe A.group (receiptFromAtlas A.exterior pad A.actual)

theorem address_cast_keeps_steps (hf : f.Monic)
    {i₀ i : J6Recovery.Addr m} {j₀ j : Fin (literalDegree m native+1)} {g₀ g : Fin 64}
    (hi : i₀=i) (hj : j₀=j) (hg : g₀=g)
    (R : GroupReceipt (ell:=ell) G hf i₀ j₀ g₀) :
    (transportRequest G hf hi hj hg R).run.steps=R.run.steps := by
  subst i
  subst j
  subst g
  rfl

theorem request_receipt_paid_from_actual_run [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hf : f.Monic) {i : J6Recovery.Addr m} {j : Fin (literalDegree m native+1)} {g : Fin 64}
    (A : ActualRequest (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
      (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) G pad i j g) :
    (requestReceipt G pad hf A).run.steps=A.actual.run.steps := by
  exact address_cast_keeps_steps (ell:=ell) G hf A.centre A.probe A.group
    (receiptFromAtlas A.exterior pad A.actual)

theorem exact_same_outer_probe [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    {i : J6Recovery.Addr m} {j : Fin (literalDegree m native+1)} {g : Fin 64}
    (A : ActualRequest (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
      (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) G pad i j g)
    (raw : List Bool) (valid : raw=List.ofFn ((rootPreset G ell).word j))
    (k : P11FullPacking.Page (a m) (K m) (Fin 64)) :
    raw=((buildRootBitBank G ell).result.read A.exterior.sample).result.val ∧
    (locate (J6R34RootAtlas.widened pad (residentPageKey m k)).result
      (A.exterior.seed pad).immutable.payload.payload.pages).result=some (A.exterior.chosenFields k) ∧
    J6R22Active.boxTransport A.exterior.field.result.exactMod
      (uvRead A.exterior.field.result.hp A.exterior.field.result.words ell (A.exterior.chosenFields k).probe) =
        prescribedNode (rootPreset G ell) (J6SourcePrecision.printed m base) ell j := by
  have h := installed_atlas_has_same_raw_probe A.exterior pad A.actual k
  have same : raw=writtenProbe (ell:=ell) G A.exterior.sample := by
    rw [A.probe]
    exact valid
  refine ⟨same.trans h.1,h.2.2.1,?_⟩
  exact h.2.2.2.trans (congrArg (prescribedNode (rootPreset G ell) (J6SourcePrecision.printed m base) ell) A.probe)

abbrev AtlasRequests (ell q rr cc dd edgew tc tj key prec tw bw : ℕ) :=
  ∀ i j g, ActualRequest (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
      (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) G pad i j g

noncomputable def sourceAtlasOracle [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (F : Frame f (J6SourcePrecision.printed m base)) (hf : f.Monic) (hh : 0<ell)
    (supply : AtlasRequests G pad ell q rr cc dd edgew tc tj key prec tw bw) : CompletedOracle G ell F hf :=
  completedOracle G hf F hh (fun i j g=>requestReceipt G pad hf (supply i j g))

theorem completed_atlas_reply [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (F : Frame f (J6SourcePrecision.printed m base)) (hf : f.Monic) (hh : 0<ell)
    (supply : AtlasRequests G pad ell q rr cc dd edgew tc tj key prec tw bw)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (raw : List Bool)
    (valid : raw=List.ofFn ((rootPreset G ell).word j)) :
    let O := sourceAtlasOracle G pad F hf hh supply
    let R := fun g=>requestReceipt G pad hf (supply i j g)
    O.reply i j raw=(completedGroups G hf F hh i j R).result ∧
    (SiteFrame G ell F i).decode (O.reply i j raw)=
      fallbackTable (G.selector ell) (G.ready ell) (G.centre ell i) hf (rootPreset G ell) j ∧
    (∀ g : Fin 64,
      let A := supply i j g
      raw=((buildRootBitBank G ell).result.read A.exterior.sample).result.val ∧
        (R g).run.steps=A.actual.run.steps) := by
  let O := sourceAtlasOracle G pad F hf hh supply
  let R := fun g=>requestReceipt G pad hf (supply i j g)
  have h := gateway_reply_exact G hf F hh (fun i j g=>requestReceipt G pad hf (supply i j g)) i j raw valid
  refine ⟨h.1,O.correct i j raw valid,?_⟩
  intro g
  let A := supply i j g
  have p : raw=((buildRootBitBank G ell).result.read A.exterior.sample).result.val := by
    rw [A.probe]
    exact h.2
  exact ⟨p,request_receipt_paid_from_actual_run G pad hf A⟩
end Chart

section Official
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {base : ℕ}
variable {ell q rr cc dd edgew tc tj key prec tw bw : ℕ}

noncomputable abbrev OfficialAtlasRequests (G : PrintedRootGuard F base) (pad : ℕ) :=
  let S := (generatedField G).result
  AtlasRequests S.rootShape pad ell q rr cc dd edgew tc tj key prec tw bw

noncomputable def atlasOfficialOracle (G : PrintedRootGuard F base) (pad : ℕ)
    (hh : 0<ell) (supply : OfficialAtlasRequests
      (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
      (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) G pad) :
    OfficialOracle G ell := by
  let S := (generatedField G).result
  letI : Fact (Irreducible (NativeProbeRing.residuePoly S.f)) := ⟨S.irreducible⟩
  exact sourceAtlasOracle S.rootShape pad S.frame.result S.presentation.monic hh supply

theorem original_J6_with_actual_atlases (G : PrintedRootGuard F base) (pad : ℕ)
    (hh : 0<ell) (supply : OfficialAtlasRequests
      (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
      (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) G pad) :
    let O := atlasOfficialOracle G pad hh supply
    bitsValue (runOfficialJ6 G ell hh O).result.val=PinnedCNF.modelCount F :=
  (original_J6 G ell hh (atlasOfficialOracle G pad hh supply)).1
end Official

#print axioms address_cast_keeps_steps
#print axioms request_receipt_paid_from_actual_run
#print axioms exact_same_outer_probe
#print axioms completed_atlas_reply
#print axioms original_J6_with_actual_atlases
end J6R34OfficialGateway
