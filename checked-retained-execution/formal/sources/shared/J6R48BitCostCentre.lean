import J6R48BitCostSite
import J6R24MeteredRecursionActiveValue

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

set_option maxRecDepth 2000

/-! An explicit additive tariff for the real R24 centre interpreter. This
charges one quotient jet, all original grouped child-word operations, and
every ordered retained coefficient scan and source-weight computation.
The centre result is not fabricated and the jet is not recomputed at each j. -/
namespace J6R48BitCost
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleCoordinates A1R10 A1R11 A1R12
open J6R22Active J6R23ScheduleWeight J6R24MeteredRecursion J6R9Recursive
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R19Retained HermiteLoss
attribute [local irreducible] J6R12Blueprint.printedParams

variable {f : ℤ[X]} {ell s : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
abbrev centreA (c : Call (PhysicalHost f ell)) := (S).levelBits c.depth
abbrev centreU (c : Call (PhysicalHost f ell)) := (S).levelWidth c.depth
abbrev centreP (c : Call (PhysicalHost f ell)) (t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c) :=
  @J6ActiveRun.registerPrecision (PhysicalHost f ell) Unit S c t
abbrev centreK (c : Call (PhysicalHost f ell)) (t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c) :=
  order c.edges (@centreU f ell s c) t.val

def centreTariff {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c}
    {t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c} {bank : Bank f}
    {q : ℕ} (D : @CentreDesc f ell s sel c d t bank) (hv : 0<ell) (high : Frame f q)
    (B : ℕ) (child : @CentreChild f ell s sel c d t bank) : ℕ :=
  let I := D.site hv child
  I.nodeBill + I.localFee (@centreA f ell s c) +
    ((List.range (@centreK f ell s c t)).map (fun j =>
      termFee f.natDegree ell (@centreP f ell s c t) q (@centreA f ell s c) B (@centreK f ell s c t) j high.hp t.val D.roster.rows)).sum +
    uvWidth high.words.length ell q+(@centreK f ell s c t)*(addCap high.words.length ell q high.hp+2) +
    tapeFee I.fw.length ell (@centreP f ell s c t) (@centreK f ell s c t)+4

theorem centre_arithmetic_measured {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c}
    {t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c} {bank : Bank f}
    {q : ℕ} (D : @CentreDesc f ell s sel c d t bank) (hv : 0<ell)
    (hf : f.Monic) (high : Frame f q) (B : ℕ)
    (hu : 0<(@centreU f ell s c)) (huM : (@centreU f ell s c)≤c.edges) (hB : commonLoss (@centreA f ell s c) c.edges (@centreU f ell s c)≤B)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (child : @CentreChild f ell s sel c d t bank) :
    (D.centre hv hf high B child).steps ≤ (D.site hv child).childBill + centreTariff (sel:=sel) (d:=d) (t:=t) D hv high B child := by
  let I := D.site hv child
  let low := bank (@centreP f ell s c t) (@register_positive f ell S (sourceDelta s) c d t)
  let J := I.run (@centreA f ell s c) t.val
  let F := D.term hv hf high B J.result
  let C := fun j : ℕ => (⟨(),termFee f.natDegree ell (@centreP f ell s c t) q (@centreA f ell s c) B (@centreK f ell s c t) j high.hp t.val D.roster.rows⟩ : Meter Unit)
  have jetFee : J.steps≤I.nodeBill+I.childBill+I.localFee (@centreA f ell s c) :=
    resident_centre_core_measured I (@centreA f ell s c) c.edges (@centreU f ell s c)
      t.property D.roster.distinct D.roster.complete D.roster.exponents
  have hj (j : ℕ) (hm : j∈List.range (@centreK f ell s c t)) : (F j).steps≤(C j).steps := by
    have hj := List.mem_range.mp hm
    have hLoss : totalLoss (@centreA f ell s c) (sourceH c.edges (@centreU f ell s c)) j t.val≤B :=
      (actual_weight_loss_le (a:=(@centreA f ell s c)) hu huM hj).trans hB
    exact weighted_term_measured low high hv hf t.property hLoss D.roster J.result hj
  have hc := bill_rel F C (List.range (@centreK f ell s c t)) hj
  have hs := (sumM_steps high.hp F (List.range (@centreK f ell s c t))).2
  rw [List.length_range] at hs
  change bill F (List.range (@centreK f ell s c t))≤((List.range (@centreK f ell s c t)).map (fun j =>
    termFee f.natDegree ell (@centreP f ell s c t) q (@centreA f ell s c) B (@centreK f ell s c t) j high.hp t.val D.roster.rows)).sum at hc
  have hmix := hs.trans (Nat.add_le_add_right (Nat.add_le_add_right hc _) _)
  have hrun := Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add jetFee hmix) (tapeFee I.fw.length ell (@centreP f ell s c t) (@centreK f ell s c t))) 4
  calc
    _ ≤ _ := hrun
    _ = (D.site hv child).childBill + centreTariff (sel:=sel) (d:=d) (t:=t) D hv high B child := by
      unfold centreTariff
      dsimp only
      ac_rfl

#print axioms centreTariff
#print axioms centre_arithmetic_measured
end J6R48BitCost

