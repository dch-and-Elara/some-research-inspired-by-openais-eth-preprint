import J7SeatPacking
import J7FullWordAssembly
import J7FullWordPrinted

/-! # Connect the source's whole words to actual typed seats and graph wires. -/
open scoped BigOperators Classical

namespace J7SeatSource
open J7SourceLabels J7SourceConditioning J7FullWordCells J7FullWordAssembly
open J7FullWordPrinted J7SeatPacking P11FullPacking

noncomputable section
set_option maxHeartbeats 1750000

def cellChartEq (A : Type*) (t : ℕ) :
    (Word A (Fin t → A) × Word A (Fin t → A)) ≃ Cell (Fin (t+1)) A :=
  (Equiv.prodCongr (wordEquiv A t) (wordEquiv A t)).trans
    ⟨fun p i => (p.1 i,p.2 i), fun q => (fun i => (q i).1, fun i => (q i).2),
      by intro p; cases p; rfl, by intro q; funext i; exact Prod.eta (q i)⟩

theorem cellChart_head {A : Type*} {t : ℕ} (x : Word A (Fin t → A) × Word A (Fin t → A)) :
    cellChartEq A t x 0 = (x.1.1,x.2.1) := by
  simp [cellChartEq, wordEquiv_retained]

def rowNode {Pair Row W : Type*} (row : W → Row) : Wire Pair W → Pin Pair ⊕ Row
  | .inl (p,_) => .inl p
  | .inr w => .inr (row w)

def colNode {Pair Col W : Type*} (col : W → OrdinaryColumn Pair Col) :
    Wire Pair W → Pin Pair ⊕ OrdinaryColumn Pair Col
  | .inl (p,false) => .inl p
  | .inl (p,true) => .inr (.inl p)
  | .inr w => .inr (col w)

/-- Nonpin is a property of the actual incident old column, not a separate
flag assigned at seating time. -/
def nonpin {Pair Col W : Type*} (col : W → OrdinaryColumn Pair Col) (e : Wire Pair W) : Prop :=
  ∃ q, colNode col e = .inr q

theorem nonpin_not_pin {Pair Col W : Type*} (col : W → OrdinaryColumn Pair Col)
    (p : Pin Pair) : ¬ nonpin col (pinEmbed Pair W p) := by
  rintro ⟨q,hq⟩
  have hh : Sum.inl p = Sum.inr q := hq
  cases hh

theorem cast_card_eq_indicator {X Y : Type*} [Fintype X] (f : X → Y) (y : Y) :
    (Nat.card {x // f x = y} : ℚ) = ∑ x : X, indicator (f x) y := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [indicator, ← Finset.sum_filter]
  simp

theorem cast_card_matching {X Y : Type*} [Fintype X] (f : X → Y)
    (good : X → Prop) (y : Y) :
    (Nat.card {x : {x // f x = y} // good x.val} : ℚ) =
      ∑ x : X, if f x = y ∧ good x then 1 else 0 := by
  classical
  let e : {x : {x // f x = y} // good x.val} ≃ {x // f x = y ∧ good x} :=
    ⟨fun x => ⟨x.val.val,x.val.prop,x.prop⟩, fun x => ⟨⟨x.val,x.prop.1⟩,x.prop.2⟩,
      by rintro ⟨⟨x,hx⟩,hx'⟩; rfl, by rintro ⟨x,hx⟩; rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [← Finset.sum_filter]
  simp

variable {A Pair Row Col W : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W]
variable {t b : ℕ}

def wordLabel (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : State A (Fin t → A) Pair Row Col) : Wire Pair W → Cell (Fin (t+1)) A :=
  fun w => cellChartEq A t (fullCell row col w z)

omit [LinearOrder A] [AddCommGroup A] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] in
theorem layout_owns_pins (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : State A (Fin t → A) Pair Row Col) (hz : ∀ d, 0 < weight d (z d))
    (p : Pin Pair) :
    ((wordLabel row col z (pinEmbed Pair W p)) 0).1 ≠
      ((wordLabel row col z (pinEmbed Pair W p)) 0).2 := by
  unfold wordLabel
  rw [cellChart_head]
  exact legal_pinOff row col z hz p

omit [AddCommGroup A] [Fintype Row] [Fintype Col] in
/-- The variance certificate gives literal, not padded-or-encoded, cell
loads. Any upper deviation radius e satisfying 32M ≤ e² suffices. -/
theorem capacity_of_deviation (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : State A (Fin t → A) Pair Row Col) (e : ℚ) (he : 0 ≤ e)
    (hcap : (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin t → A) + e ≤ b * (2:ℚ)^(t+1))
    (hdev : ∀ c, ((∑ w : Wire Pair W, indicator (fullCell row col w z) c) -
      (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin t → A))^2 ≤ e^2) :
    ∀ c, Nat.card {w // wordLabel row col z w = c} ≤ b*2^(t+1) := by
  classical
  intro c
  have dev := hdev ((cellChartEq A t).symm c)
  have hsum : (Nat.card {w // wordLabel row col z w = c} : ℚ) =
      ∑ w : Wire Pair W, indicator (fullCell row col w z) ((cellChartEq A t).symm c) := by
    rw [cast_card_eq_indicator]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold wordLabel indicator
    by_cases h : fullCell row col w z = (cellChartEq A t).symm c
    · rw [h,Equiv.apply_symm_apply]
      simp
    · have hn : (cellChartEq A t) (fullCell row col w z) ≠ c :=
        fun he => h ((Equiv.eq_symm_apply _).2 he)
      simp [h,hn]
  have hj : (Nat.card {w // wordLabel row col z w = c} : ℚ) -
      (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin t → A) ≤ e := by
    rw [← hsum] at dev
    by_contra! hbad
    have hp : 0 <
      ((Nat.card {w // wordLabel row col z w = c} : ℚ) -
          (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin t → A) - e) *
      ((Nat.card {w // wordLabel row col z w = c} : ℚ) -
          (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin t → A) + e) :=
      mul_pos (sub_pos.mpr hbad) (by linarith)
    nlinarith
  have hb : (Nat.card {w // wordLabel row col z w = c} : ℚ) ≤ b*(2:ℚ)^(t+1) := by linarith
  exact_mod_cast hb

omit [AddCommGroup A] [Fintype Row] [Fintype Col] in
/-- Source assignment -> full-word physical seating with matching endpoints.
The matching supplied here will be obtained by local fair marks; this
interface does not assume any equivalent output representation or fake slot. -/
theorem seat_source (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : State A (Fin t → A) Pair Row Col) (hz : ∀ d, 0 < weight d (z d))
    (matching : Set (Wire Pair W))
    (hrow : matching.InjOn (rowNode row)) (hcol : matching.InjOn (colNode col))
    (hpin : ∀ w ∈ matching, nonpin col w)
    (cap : ∀ c, Nat.card {w // wordLabel row col z w = c} ≤ b*2^(t+1))
    (enough : ∀ c, 2*b ≤ Nat.card {w : {w // wordLabel row col z w = c} // w.val ∈ matching}) :
    ∃ j : Wire Pair W ↪ Physical (t+1) b A,
      (∀ w, physicalCell (balancedMask (t+1) b) (j w) = wordLabel row col z w) ∧
      (∀ w, isEnd (j w) → w ∈ matching) ∧
      (∀ s, isEnd s → ∃ w, j w = s) ∧
      (Set.InjOn (rowNode row) {w | isEnd (j w)}) ∧
      (Set.InjOn (colNode col) {w | isEnd (j w)}) ∧
      (∀ p : Pin Pair, ¬isEnd (j (pinEmbed Pair W p)) ∧
        ((physicalCell (balancedMask (t+1) b) (j (pinEmbed Pair W p))) 0).1 ≠
          ((physicalCell (balancedMask (t+1) b) (j (pinEmbed Pair W p))) 0).2) := by
  obtain ⟨j,hc,he,hs⟩ := packet_seating (by omega : 0 < t+1)
    (wordLabel row col z) (fun w => w ∈ matching) cap enough
  refine ⟨j,hc,he,hs,?_,?_,?_⟩
  · intro x hx y hy h
    exact hrow (he x hx) (he y hy) h
  · intro x hx y hy h
    exact hcol (he x hx) (he y hy) h
  · intro p
    refine ⟨fun he' => nonpin_not_pin col p (hpin _ (he _ he')),?_⟩
    rw [hc]
    exact layout_owns_pins row col z hz p

#print axioms cellChart_head
#print axioms cast_card_eq_indicator
#print axioms cast_card_matching
#print axioms capacity_of_deviation
#print axioms seat_source

end
end J7SeatSource
