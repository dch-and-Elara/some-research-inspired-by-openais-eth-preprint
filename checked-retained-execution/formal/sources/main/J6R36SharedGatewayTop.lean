import J6R36SharedGatewayAll
import J6R36SharedGatewayDelta

/-! Run the original query encoder, native interpolation and signed
readout with the same held root cache and with the *paid* grouped
backend. The exact fee separates one setup, pre-existing original
oracle-boundary overhead, and the actual reply occurrences. -/
namespace J6R36SharedGateway
open scoped Polynomial Classical BigOperators
open Polynomial Std.Sat AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J7R10Plant J6R24LegalLayout J6R24MeteredRecursion
open J6R34RootAtlas J6R35GatewayPreparation J6R34OfficialGateway J6R33OriginalJ6
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R22Active J6R22RootReadout
open J6R28GeneratedRootFrame J6R29BinaryFieldSearch J6R25StableCensus
set_option maxHeartbeats 18500000
set_option maxRecDepth 2850
set_option linter.unusedSectionVars false

theorem sum_requests {A B : Type*} (x : List A) (y : List B) (g : A→B→ℕ) :
    ((x.flatMap (fun a=>y.map (Prod.mk a))).map (fun p=>g p.1 p.2)).sum=
      (x.map (fun a=>(y.map (g a)).sum)).sum := by
  induction x with
  | nil => rfl
  | cons a z ih =>
    simp [List.flatMap_cons,List.map_append,List.sum_append,List.map_map,Function.comp_def,ih]

theorem trace_bill_exact (m d : ℕ) (q : Fin (m+1)→Fin (d+1)→ℕ) :
    ((requestTrace m d).map (fun p=>q p.1 p.2)).sum=
      ∑ i : Fin (m+1),((probeOrder (d+1)).map (q i)).sum := by
  unfold requestTrace
  rw [sum_requests]
  simp only [probeOrder,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

section CNF
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {F : CNF V} {base ell q rr cc dd edgew tc tj key prec tw bw : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "pm" => J6SourcePrecision.printed
variable (G : RootShape f (ms F) (printedHalf (ms F)) base (literalNativeSize F)
  (printedRankWidth (ms F)) (physicalPlant (J7R10Readout.H F)) (constantRootWord (ms F)))
variable (C : CommonInputs (T:=physicalPlant (J7R10Readout.H F)) (f:=f) (base:=base) ell q rr cc dd)
variable (pad : ℕ)
variable (supply : SharedRequests G C pad edgew tc tj key prec tw bw)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

noncomputable def finishSites (sites : J6Recovery.Addr (ms F)→Meter (Block C.field.result ell)) :
    Meter (Word (printedAnswerWidth (ms F) base)) :=
  let m := ms F
  let w := constantRootWord m
  let wn := printed_readout_fits m (qs F) base w
  countFromMeasuredSlots C.field.result wn.1 wn.2.1 m (printedHalf m) (qs F) (printedRankWidth m)
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w)) sites

variable (cache : ActualRootPreparation G ell q)
variable (exactCache : cache=(CommonInputs.make (G:=G) C).result)

noncomputable def implementedSlot : SlotProgram (ell:=ell) (F:=C.field.result) G :=
  fun i j _raw=>cachedSlot cache exactCache supply i j

noncomputable def frontUsingCache : Meter (Word (printedAnswerWidth (ms F) base)) :=
  finishSites C (fun i=>oracleSite G cache.probes (cachedOracle cache exactCache supply) C.positive i)

noncomputable def paidUsingCache : Meter (Word (printedAnswerWidth (ms F) base)) :=
  finishSites C (fun i=>paidSite G cache.probes (implementedSlot G C pad supply cache exactCache) C.hf C.positive i)

noncomputable def actualReplyBill : ℕ :=
  ((requestTrace (ms F) (literalDegree (ms F) (literalNativeSize F))).map
    (fun addr=>(cachedSlot cache exactCache supply addr.1 addr.2).steps)).sum

theorem operation_costs_reach_final_word :
    Delta (paidUsingCache G C pad supply cache exactCache)
      (frontUsingCache G C pad supply cache exactCache)
      (actualReplyBill G C pad supply cache exactCache) := by
  let m := ms F
  let w := constantRootWord m
  let n := literalDegree m (literalNativeSize F)
  let wn := printed_readout_fits m (qs F) base w
  let O := cachedOracle cache exactCache supply
  let I := implementedSlot G C pad supply cache exactCache
  let cost := fun i j=>(cachedSlot cache exactCache supply i j).steps
  have legal (i : J6Recovery.Addr m) (j : Fin (n+1)) (raw : List Bool)
      (h : raw=List.ofFn ((rootPreset G ell).word j)) :
      (I i j raw).result=O.reply i j raw :=
    (cached_all64_reply_equals_fresh cache exactCache supply i j raw (h.trans (cache.probes.consistent j).symm)).1.symm
  have T := gather_delta C.field.result wn.1 wn.2.1 m (printedHalf m) (qs F) (printedRankWidth m)
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w))
    (fun i=>paidSite G cache.probes I C.hf C.positive i)
    (fun i=>oracleSite G cache.probes O C.positive i)
    (fun i=>((probeOrder (n+1)).map (cost i)).sum)
    (fun i=>actual_paid_site_delta G cache.probes I O legal C.positive i)
  have id : actualReplyBill G C pad supply cache exactCache=
    ∑ i : Fin (m+1),((probeOrder (n+1)).map (cost i)).sum := trace_bill_exact m n cost
  rw [id]
  exact T

noncomputable def ordinaryFrontend : Meter (Word (printedAnswerWidth (ms F) base)) :=
  let m := ms F
  let w := constantRootWord m
  let W := printed_readout_fits m (qs F) base w
  oracleCount F base (printedHalf m) (literalNativeSize F) (printedRankWidth m)
    (printedFactorWidth m (qs F)) (printedAnswerWidth m base) w G C.field.result C.hf C.positive
    W.1 W.2.1 (cachedOracle cache exactCache supply)

theorem original_frontend_and_no_duplicate_bank :
    (ordinaryFrontend G C pad supply cache exactCache).result=
      (frontUsingCache G C pad supply cache exactCache).result ∧
    (ordinaryFrontend G C pad supply cache exactCache).steps=
      (frontUsingCache G C pad supply cache exactCache).steps+(buildRootBitBank G ell).steps+4 := by
  subst cache
  exact ⟨rfl,rfl⟩

noncomputable def runWithOneSharedRoot : Meter (Word (printedAnswerWidth (ms F) base)) :=
  let made := CommonInputs.make (G:=G) C
  let reply := paidUsingCache G C pad supply made.result rfl
  ⟨reply.result,made.steps+reply.steps+4⟩

theorem exact_source_count_and_separated_bill (basePositive : 0<base) :
    let made := CommonInputs.make (G:=G) C
    let out := runWithOneSharedRoot G C pad supply
    let front := frontUsingCache G C pad supply made.result rfl
    let extra := actualReplyBill G C pad supply made.result rfl
    let m := ms F
    let pads := (exactPadOrder m (K m) (printedHalf m) (constantRootWord m)).length
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps=made.steps+front.steps+extra+4 ∧
      front.steps+(buildRootBitBank G ell).steps+4≤
        reductionFee m f.natDegree (literalNativeSize F) (printedRankWidth m) (printedHalf m)
          (printedFactorWidth m (qs F)) (printedAnswerWidth m base) ell (pm m base) pads C.field.result.hp := by
  let m := ms F
  let w := constantRootWord m
  let W := printed_readout_fits m (qs F) base w
  let R := CommonInputs.make (G:=G) C
  let O := cachedOracle R.result rfl supply
  have budget := supplied_completed_oracle_count (f:=f) (ell:=ell) F base (printedHalf m) (literalNativeSize F)
    (printedRankWidth m) (printedFactorWidth m (qs F)) (printedAnswerWidth m base) w G
    (printed_rank_width m).1 C.field.result C.hf basePositive C.positive W.1 W.2.1 O W.2.2.1 W.2.2.2
  obtain ⟨val,bound,_,_⟩ := budget
  have old := original_frontend_and_no_duplicate_bank G C pad supply R.result rfl
  have paid := operation_costs_reach_final_word G C pad supply R.result rfl
  refine ⟨?_,?_,?_⟩
  · exact (congrArg (fun (x : Word (printedAnswerWidth m base))=>bitsValue x.val)
      (paid.value.trans old.1.symm)).trans val
  · change R.steps+(paidUsingCache G C pad supply R.result rfl).steps+4=
      R.steps+(frontUsingCache G C pad supply R.result rfl).steps+
        actualReplyBill G C pad supply R.result rfl+4
    rw [paid.fee]
    omega
  · rw [←old.2]
    exact bound
end CNF

#print axioms sum_requests
#print axioms trace_bill_exact
#print axioms operation_costs_reach_final_word
#print axioms original_frontend_and_no_duplicate_bank
#print axioms exact_source_count_and_separated_bill
end J6R36SharedGateway
