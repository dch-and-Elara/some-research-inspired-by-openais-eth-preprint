import P5NativeEntryDensity
import P5MainIteratorAsymptotic
import P5MainIteratorPrinted

/-! The original signed-unit entry, with only the three sparse-evaluator
iterators retuned as in F.A4.  Paid Taylor, attainable measurement and
local assignment visits are explicit. This is not a bound for a
redesigned sparse solver.  The input is entered as a 2-CNF. -/
namespace Paper5.NativeEntry
open scoped BigOperators Classical
open P5MainIterator

structure RetunedScan {n : ℕ} (A : Rows n) (T : ℕ) (κ : ℝ) where
  copies : ℕ
  nodes : ℕ
  groups : ℕ
  width : ℕ
  omitted : Finset ℕ
  layout : SourceLayout (Ports A) (Free A) (Factors A) (Fin copies)
    (Fin nodes) (Fin groups)
  ownerOK : ∀ e,layout.placement.owner e=portOwner e
  factorOK : ∀ e,layout.factor e=portFactor e
  rGuard : 2≤groups
  RGuard : 1≤width
  QGuard : width<nodes
  omitBound : omitted.card≤width
  cells : ∀ u,cellLoad layout u*Nat.card (WordCell (Fin nodes) (Fin groups))≤
    2*Nat.card (Ports A)
  tm : Fin nodes
  tg : Fin nodes
  g : Fin groups
  q : ℕ
  order : ⌊κ*(dim A:ℝ)*(width:ℝ)/(nodes:ℝ)⌋₊≤q
  visits : SourceVisits (fun j=>j∉omitted) layout tm tg g q T

inductive RetunedSparseReceipt {n : ℕ} (A : Rows n) (T : ℕ) (κ : ℝ) where
  | trivial : (retained A).card=0 → RetunedSparseReceipt A T κ
  | fallback : ExhaustiveReceipt n T → RetunedSparseReceipt A T κ
  | active : RetunedScan A T κ → RetunedSparseReceipt A T κ

inductive RetunedEntryReceipt {n : ℕ} (sgn : Fin n→Bool) (T : ℕ) (κ : ℝ) where
  | preliminary : ExhaustiveReceipt n T → RetunedEntryReceipt sgn T κ
  | leaf (h : 2≤printedGroups n) (A₀ : Rows n) : A₀.length≤3*n →
      (∀ r∈A₀,(support r).card≤hashD₀ n (sparB₂ (printedGroups n) h)) →
      (run : @Greedy n (hashP n (sparB₂ (printedGroups n) h)) sgn A₀) →
      (∀ j : Fin (3*n),∀ γ : Candidate n (hashP n (sparB₂ (printedGroups n) h)),
        RetunedSparseReceipt (run.rows j++[candidateRow γ]) T κ) →
      RetunedEntryReceipt sgn T κ

theorem binary_scale_agrees (n : ℕ) :
    binaryScale n=(n:ℝ)*targetScale (logTwo (n:ℝ)) (logTwo (logTwo (n:ℝ))) := by
  unfold binaryScale logTwo targetScale Real.logb
  ring

theorem source_taylor_lower {n : ℕ} (A : Rows n) (R Q : ℕ)
    (hA : (matrix A).rank=n) (hn : 20≤n) :
    ⌊(1:ℝ)*(Fintype.card (Free A):ℝ)*(R:ℝ)/(Q:ℝ)⌋₊≤shapeDegree 2 A*R/Q := by
  simp only [one_mul,free_card,←Nat.cast_mul]
  rw [real_floor_ratio_nat]
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  have hh : dim A≤(retained A).card := (branch_has_equations A hn hA).2
  unfold shapeDegree
  omega

set_option maxHeartbeats 9000000 in
theorem retuned_rational_entry_eventual_cost (κ : ℝ) (hκ : 0<κ) :
    ∃ c : ℝ, 0<c ∧ ∃ n₀ : ℕ, ∀ n≥n₀,∀ (sgn : Fin n→Bool) (T : ℕ),
      RetunedEntryReceipt sgn T κ → c*binaryScale n≤logTwo T := by
  obtain ⟨c,hc,m,FA⟩ := eventual_FA4 (6:ℝ) κ (by norm_num) hκ
  obtain ⟨p,HP⟩ := preliminary_eventual_unclipped
  obtain ⟨d,HD⟩ := eventually_branch_density
  let a := min (c/144) (1/2:ℝ)
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  refine ⟨a,ha,max (max 20 (2*m)) (max p d),?_⟩
  intro n hn sgn T tr
  have h20 : 20≤n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hm : 2*m≤n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hp : p≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hLarge : d≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hNon : 0≤binaryScale n := by unfold binaryScale; positivity
  have hFallback (w : ExhaustiveReceipt n T) : a*binaryScale n≤logTwo T := by
    have h : a*binaryScale n≤(1/2:ℝ)*binaryScale n :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hNon
    have hx := exhaustive_log_cost w
    have bb := HP n hp
    linarith only [h,hx,bb]
  cases tr with
  | preliminary w => exact hFallback w
  | leaf h A₀ hlen hwidth run allCalls =>
    let B := sparB₂ (printedGroups n) h
    have hB : 0<B := (literal_unit_source_B_bound h).1
    obtain ⟨hP,hPD⟩ := actual_params (n:=n) hB
    let j : Fin (3*n) := ⟨n-1,by omega⟩
    let A := run.rows j++[candidateRow (run.chosen j)]
    have hStep : run.rows n=A := by
      have hx := run.step j j.isLt
      have ht : j.val+1=n := by dsimp [j]; omega
      rwa [ht] at hx
    have hA : (matrix A).rank=n := by
      rw [←hStep]
      exact greedy_full_rank run hP n le_rfl (by omega)
    have hlenA : A.length≤6*n := by
      rw [←hStep,greedy_length run n (by omega)]
      omega
    have hwidthA : ∀ r∈A,(support r).card≤hashD₀ n B := by
      rw [←hStep]
      exact greedy_width run n (by omega) hPD hwidth
    have hTest := (branch_has_equations A h20 hA).2
    have hHalf := dim_at_least_half A h20
    have hDim := dim_add_fixed A
    have hS := binary_half_comparison (d:=dim A) (n:=n) (by omega) (by omega) hHalf
    cases allCalls j (run.chosen j) with
    | trivial hNo =>
      change (retained A).card=0 at hNo
      omega
    | fallback w => exact hFallback w
    | active W₀ =>
      let W : RetunedScan A T κ := W₀
      have hDensity := HD n hLarge A h hlenA hwidthA
      have hSpatial : (Fintype.card (Ports A):ℝ)≤
          (Fintype.card (Free A):ℝ)*(logTwo (Fintype.card (Free A):ℝ))^(6:ℝ) := by
        rw [ports_count,free_card,show (6:ℝ)=((6:ℕ):ℝ) by norm_num,
          Real.rpow_natCast]
        exact hDensity
      have hCut : m≤Fintype.card (Free A) := by
        rw [free_card]
        omega
      have H := FA W.layout W.tm W.tg W.g W.q T W.width
        W.omitted W.visits hCut hSpatial
        (by simpa using W.rGuard) W.RGuard (by simpa using W.QGuard) W.omitBound
        (by simpa only [←Nat.card_eq_fintype_card] using W.cells)
        (by simpa only [free_card,Fintype.card_fin] using W.order)
      rw [free_card,mul_assoc,←binary_scale_agrees] at H
      calc
        a*binaryScale n ≤ (c/144)*binaryScale n :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hNon
        _ ≤ (c/144)*(144*binaryScale (dim A)) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
        _ = c*binaryScale (dim A) := by ring
        _ ≤ _ := H

#print axioms binary_scale_agrees
#print axioms source_taylor_lower
#print axioms retuned_rational_entry_eventual_cost
end Paper5.NativeEntry