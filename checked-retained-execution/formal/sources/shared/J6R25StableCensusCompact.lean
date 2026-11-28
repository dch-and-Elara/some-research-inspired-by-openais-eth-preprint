
import J6R25StableCensusPadTape

/-! Whole raw, charged padding-pair bank for the actually chosen
stable chart, directly from its compact planted label and dimensions. -/
namespace J6R25StableCensus
open scoped Classical BigOperators
open P11FullPacking J6Mesh J6OrientedHost J6RecursiveOrientation J6R23PaddingCensus
open J6R24LegalLayout J6R14LayoutCost AOracleMachineTime J6R12CollisionEdges
set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false

def allPairsPadFee (a b l q : ℕ) :=
  b*l*padStepFee a q+padCellExtra a q+48*(a+q+4)*(b*l)+6

def sweepPadCells (a b l q m : ℕ) (diag : CellWord) : List CellWord→Meter (List (RawCol a q))
  | [] => ⟨[],5⟩
  | k::ks =>
    let C := localCellPairs a b l q m diag k
    let tail := sweepPadCells a b l q m diag ks
    ⟨C.result++tail.result,C.steps+tail.steps+48*(a+q+4)*(b*l)+6⟩

private theorem append_match {A B : Type*} {r : A→B→Prop}
    {x y : List A} {u v : List B} (h : List.Forall₂ r x u) (k : List.Forall₂ r y v) :
    List.Forall₂ r (x++y) (u++v) := by
  induction h with
  | nil => exact k
  | cons a hs ih => exact .cons a ih

theorem sweep_pad_cell_receipt (a b l q m : ℕ) (hq : 0<q) (ha : a≤q) (cap : b*2^a<2^q)
    (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a) (cells : List (CellType a)) :
    let C := deterministicLegal ha cap.le w hm hL
    let out := sweepPadCells a b l q m (wordCell (diagonal w)) (cells.map wordCell)
    List.Forall₂ (fun (row : RawCol a q) (d : J6OrientedHost.Pad w m b l) =>
      row.represents (pageCode (q-a)) (fun side=>C.seats (.inr (d,side))))
      out.result (cells.flatMap (padsInCell m b l w)) ∧
    out.steps≤5+cells.length*allPairsPadFee a b l q := by
  let C := deterministicLegal ha cap.le w hm hL
  induction cells with
  | nil => simp [sweepPadCells]
  | cons c cs ih =>
    obtain ⟨t,ft⟩ := ih
    have p := local_realizes_pairs a b l q m hq ha cap w hm hL c
    constructor
    · exact append_match p t
    · have hLocal := (local_cell_pairs a b l q m hq ha cap w hm hL c).2
      have hN : padSpan m b l w c≤b*l := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have k := Nat.mul_le_mul_right (padStepFee a q) hN
      change (localCellPairs a b l q m (wordCell (diagonal w)) (wordCell c)).steps+
        (sweepPadCells a b l q m (wordCell (diagonal w)) (cs.map wordCell)).steps+
        48*(a+q+4)*(b*l)+6≤5+(cs.length+1)*allPairsPadFee a b l q
      rw [Nat.add_mul,one_mul]
      unfold allPairsPadFee at ft ⊢
      omega

def stablePadTape (a b l q m : ℕ) (diag : CellWord) : Meter (List (RawCol a q)) :=
  let keys := allPairsMachine (6*a)
  let pairs := sweepPadCells a b l q m diag keys.result
  ⟨pairs.result,keys.steps+pairs.steps+7⟩

def stablePadBudget (a b l q : ℕ) :=
  allPairsCap (6*a)+5+(2^(6*a)*2^(6*a))*allPairsPadFee a b l q+7

theorem stable_pad_tape_exact (m l q : ℕ) (hq : 0<q) (ha : a m≤q)
    (cap : K m*L m<2^q) (w : Fin (a m)→Fin 64) (hm : m≤K m) (hL : 2*l=L m) :
    let C := deterministicLegal ha cap.le w hm hL
    let out := stablePadTape (a m) (K m) l q m (wordCell (diagonal w))
    (exactPadOrder m (K m) l w).Nodup ∧
    (exactPadOrder m (K m) l w).toFinset=Finset.univ ∧
    realizesLegalLayout m l w hm hL C (pageCode (q-a m)) out.result (exactPadOrder m (K m) l w) ∧
    out.steps≤stablePadBudget (a m) (K m) l q := by
  obtain ⟨nd,all⟩ := exact_pad_order m (K m) l w
  obtain ⟨hkeys,ckeys⟩ := allPairsMachine_exact (6*a m)
  have k := (typed_cells_exact (a m)).2.2
  have len := congrArg List.length k
  rw [List.length_map,allPairs_len] at len
  obtain ⟨hnow,cnow⟩ := sweep_pad_cell_receipt (a m) (K m) l q m hq ha cap w hm hL (typedCells (a m))
  rw [k] at hnow cnow
  refine ⟨nd,all,?_,?_⟩
  · dsimp only [stablePadTape]
    rw [hkeys]
    exact hnow
  · dsimp only [stablePadTape]
    rw [hkeys,len] at *
    unfold stablePadBudget
    omega

theorem stable_page_width (a b q : ℕ) (ha : a≤q) (cap : b*2^a<2^q) :
    b≤2^(q-a) := by
  have E : (2:ℕ)^q=2^(q-a)*2^a := by
    rw [←pow_add,Nat.sub_add_cancel ha]
  rw [E] at cap
  exact (Nat.lt_of_mul_lt_mul_right cap).le

#print axioms sweep_pad_cell_receipt
#print axioms stable_pad_tape_exact
#print axioms stable_page_width
end J6R25StableCensus
