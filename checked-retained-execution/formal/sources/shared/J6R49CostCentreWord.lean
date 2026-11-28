import J6R49CostCentreBill
import J6R49DFSCentreBase
import J6R48BitCostCentre

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 19000000
set_option maxRecDepth 2700

/-! Actual R49 centre from the tape builder to its retained coefficients.
The output coefficient loop consumes the same cached jet; neither the
tape nor the streamed samples are rebuilt per weighted coefficient. -/
namespace J6R49Cost
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R23ScheduleWeight J6R19Retained HermiteLoss J6R48BitCost J6R49DFS

attribute [local irreducible] J6R12Blueprint.printedParams

variable {f : ℤ[X]} {ell s : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

noncomputable def streamCentreTariff {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c}
    {t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c} {bank : Bank f}
    {q highPrec : ℕ} (J : @CentreMachine f ell s sel c d t bank q)
    (hv : 0<ell) (high : Frame f highPrec) (B : ℕ) : ℕ :=
  let F := J.low
  let k := J.window
  let node := fun z : Probe S c => padCost (encodeProbe F.hp hv (J.masks z).result) (J.masks z).steps
  J.tape.steps+
    ((J9PrintedSchedule.probeCount c.edges (2^(@centreA f ell s c)))*streamedProbeTariff F J.tape.result+
      normalizerFee F.words.length ell (@centreP f ell s c t) (@centreA f ell s c) k F.hp J.roster.rows+
      ((probeOrder (J9PrintedSchedule.probeCount c.edges (2^(@centreA f ell s c)))).map (needsAt node)).sum+
      interpExtra F.words.length ell (@centreP f ell s c t) k (J9PrintedSchedule.probeCount c.edges (2^(@centreA f ell s c))) F.hp+quotientFee F.words.length ell (@centreP f ell s c t) k F.hp+4)+
    ((List.range k).map (fun j => termFee f.natDegree ell (@centreP f ell s c t) highPrec (@centreA f ell s c) B k j high.hp t.val J.roster.rows)).sum+
    uvWidth high.words.length ell highPrec+k*(addCap high.words.length ell highPrec high.hp+2)+
    tapeFee F.words.length ell (@centreP f ell s c t) k+4

theorem actual_stream_centre_all_arithmetic {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c}
    {t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c} {bank : Bank f}
    {q highPrec : ℕ} (J : @CentreMachine f ell s sel c d t bank q)
    (hq : 0<q) (hv : 0<ell) (hf : f.Monic) (high : Frame f highPrec) (B : ℕ)
    (hu : 0<(@centreU f ell s c)) (huM : (@centreU f ell s c) ≤ c.edges) (hB : commonLoss (@centreA f ell s c) c.edges (@centreU f ell s c) ≤ B)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (child : @CentreChild f ell s sel c d t bank) :
    (J.runCentre hq hv hf high B child).steps  ≤ 
      centreChildBill J.low child+streamCentreTariff (sel:=sel) (d:=d) (t:=t) J hv high B := by
  let F := J.low
  let k := J.window
  let n := (J9PrintedSchedule.probeCount c.edges (2^(@centreA f ell s c)))
  let node := fun z : Probe S c => padCost (encodeProbe F.hp hv (J.masks z).result) (J.masks z).steps
  let core := J.centreJet hq hv child
  let term := J.centreTerm hv hf high B core.result
  let jFee := fun j=>(⟨(),termFee f.natDegree ell (@centreP f ell s c t) highPrec (@centreA f ell s c) B k j high.hp t.val J.roster.rows⟩ : Meter Unit)
  let hk : 0<k := active_order_pos (@centreA f ell s c) c.edges (@centreU f ell s c) t.val t.property
  have runBill := direct_streamed_centre_arithmetic_bill F J.tape.result hq hv hk J.masks J.roster.rows child
    J.roster.distinct J.roster.complete J.roster.exponents
  have hcore : core.steps  ≤  centreChildBill F child+
      (n*streamedProbeTariff F J.tape.result+
        normalizerFee F.words.length ell (@centreP f ell s c t) (@centreA f ell s c) k F.hp J.roster.rows+
        ((probeOrder n).map (needsAt node)).sum+
        interpExtra F.words.length ell (@centreP f ell s c t) k n F.hp+quotientFee F.words.length ell (@centreP f ell s c t) k F.hp+4) :=
    runBill
  have ht (j : ℕ) (hj : j∈List.range k) : (term j).steps  ≤  (jFee j).steps := by
    have h := List.mem_range.mp hj
    have hLoss : totalLoss (@centreA f ell s c) (sourceH c.edges (@centreU f ell s c)) j t.val ≤ B :=
      (actual_weight_loss_le (a:=(@centreA f ell s c)) hu huM h).trans hB
    exact weighted_term_measured F high hv hf t.property hLoss J.roster core.result h
  have hT := bill_rel term jFee (List.range k) ht
  have hSum := (sumM_steps high.hp term (List.range k)).2
  rw [List.length_range] at hSum
  change (J.runCentre hq hv hf high B child).steps  ≤  _
  calc
    _  ≤  J.tape.steps+core.steps+
          (bill jFee (List.range k)+uvWidth high.words.length ell highPrec+
            k*(addCap high.words.length ell highPrec high.hp+2))+
          tapeFee F.words.length ell (@centreP f ell s c t) k+4 :=
      Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_left (hSum.trans
          (Nat.add_le_add_right (Nat.add_le_add_right hT _) _)) _) _) _
    _  ≤  _ := by
      unfold streamCentreTariff
      dsimp only
      change _  ≤  centreChildBill F child+
        (J.tape.steps+(n*streamedProbeTariff F J.tape.result+
          normalizerFee F.words.length ell (@centreP f ell s c t) (@centreA f ell s c) k F.hp J.roster.rows+
          ((probeOrder n).map (needsAt node)).sum+
          interpExtra F.words.length ell (@centreP f ell s c t) k n F.hp+quotientFee F.words.length ell (@centreP f ell s c t) k F.hp+4)+
        bill jFee (List.range k)+uvWidth high.words.length ell highPrec+
          k*(addCap high.words.length ell highPrec high.hp+2)+tapeFee F.words.length ell (@centreP f ell s c t) k+4)
      omega

#print axioms streamCentreTariff
#print axioms actual_stream_centre_all_arithmetic
end J6R49Cost

