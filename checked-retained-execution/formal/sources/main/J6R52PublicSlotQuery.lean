import J6R52PublicSlotRun
import J6R36SharedGatewayDelta

/-! The real completed slot, not one of its 64 group children:
same exterior centre/probe addresses, same selected chart, actual
online runs and their actual enclosing product/copy bill. -/
namespace J6R52PublicSlot
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R12
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion J6R22Active
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R33OriginalJ6
open J6R32RootGeneratedRegistryInputs J6R34OfficialGateway J6R36SharedGateway J6R19Retained J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3150
set_option maxHeartbeats 21000000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native ell key prec tw bw page speed : ℕ}
variable {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)) (hf : f.Monic)
variable (F : Frame f (J6SourcePrecision.printed m base)) (hv : 0<ell)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

abbrev GroupPrograms (ell key prec tw bw page speed : ℕ) :=
  ∀ i j g, PublicGroup (ell:=ell) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw)
    (page:=page) (speed:=speed) G hf i j g

variable (R : GroupPrograms G hf ell key prec tw bw page speed)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))

def receiptsAt (g : Fin 64) : GroupReceipt (ell:=ell) G hf i j g :=
  actualGroupReceipt G hf i j g (R i j g) (F.natDegree hf ▸ F.sizePos)

def slotBody : Meter (Block (SiteFrame G ell F i) ell) :=
  completedGroups G hf F hv i j (receiptsAt G hf F R i j)

theorem slot_body_is_original_completed_reply :
    (SiteFrame G ell F i).decode (slotBody G hf F hv R i j).result =
      fallbackTable (G.selector ell) (G.ready ell) (G.centre ell i) hf (rootPreset G ell) j :=
  (completed_groups_exact G hf F hv i j (receiptsAt G hf F R i j)).1

theorem slot_body_charges_original_online_groups :
    let p := (exteriorChild G ell i j (0:Fin 64)).prec
    let E := SiteFrame G ell F i
    (slotBody G hf F hv R i j).steps ≤
      (∑ g : Fin 64,(groupRun G hf i j g (R i j g)).steps) +
        64*(boxFee f.natDegree ell p p+4) + tupleExtra E.words.length ell p 64 := by
  let p := (exteriorChild G ell i j (0:Fin 64)).prec
  let E := SiteFrame G ell F i
  let charged := fun g=>groupOnSite G hf F i j g (receiptsAt G hf F R i j g)
  have agg := (completed_groups_exact G hf F hv i j (receiptsAt G hf F R i j)).2
  change (slotBody G hf F hv R i j).steps≤bill charged (groupOrder 64)+
    tupleExtra E.words.length ell p 64 at agg
  refine agg.trans (Nat.add_le_add_right ?_ _)
  unfold bill groupOrder
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply]
  calc
    (∑ g : Fin 64,(charged g).steps) ≤
        ∑ g : Fin 64,((groupRun G hf i j g (R i j g)).steps+(boxFee f.natDegree ell p p+4)) :=
      Finset.sum_le_sum (fun g _=>(group_on_site_exact G hf F i j g (receiptsAt G hf F R i j g)).2)
    _ = _ := by simp [Finset.sum_add_distrib,p]

variable (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)

def paidSlotProgram : SlotProgram (ell:=ell) (F:=F) G :=
  fun i j raw =>
    let expected := A.read j
    let test := eqRawBits raw expected.result.val
    if test.result then
      let run := slotBody G hf F hv R i j
      ⟨run.result,expected.steps+test.steps+run.steps+4⟩
    else
      let reject := zeroM (ell:=ell) (SiteFrame G ell F i).hp
      ⟨reject.result,expected.steps+test.steps+reject.steps+4⟩

theorem legal_slot_checks_the_source_bits (raw : List Bool)
    (legal : raw=List.ofFn ((rootPreset G ell).word j)) :
    let expected := A.read j
    let test := eqRawBits raw expected.result.val
    let run := slotBody G hf F hv R i j
    paidSlotProgram G hf F hv R A i j raw=
      ⟨run.result,expected.steps+test.steps+run.steps+4⟩ := by
  have same : raw=(A.read j).result.val := legal.trans (A.consistent j).symm
  have test := (eq_raw_bits_exact raw (A.read j).result.val).1.mpr same
  unfold paidSlotProgram
  dsimp only
  rw [if_pos test]

def sourceOracle : CompletedOracle G ell F hf :=
  completedOracle G hf F hv (receiptsAt G hf F R)

theorem legal_paid_slot_matches_oracle (raw : List Bool)
    (legal : raw=List.ofFn ((rootPreset G ell).word j)) :
    (paidSlotProgram G hf F hv R A i j raw).result=
      (sourceOracle G hf F hv R).reply i j raw := by
  have h := (gateway_reply_exact G hf F hv (receiptsAt G hf F R) i j raw legal).1
  exact (congrArg Meter.result (legal_slot_checks_the_source_bits G hf F hv R i j A raw legal)).trans h.symm

#print axioms slot_body_is_original_completed_reply
#print axioms slot_body_charges_original_online_groups
#print axioms legal_slot_checks_the_source_bits
#print axioms legal_paid_slot_matches_oracle
end
end J6R52PublicSlot
