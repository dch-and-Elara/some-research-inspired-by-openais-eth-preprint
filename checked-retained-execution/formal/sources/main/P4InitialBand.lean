import PrecisionMenu
import Mathlib.Tactic

/-! The exact initial band in (P4), rather than only the unrestricted
coefficient-generating identity. Positive modes behave as singletons in
the entire band; packet/tile bounds are kept separate from degree. -/

namespace P4InitialBand
open scoped BigOperators Polynomial

variable {I : Type*} [Fintype I]

def order (e : I → ℕ) : ℕ := ∑ i, e i

def value (cost e : I → ℕ) : ℕ := ∑ i, cost i * e i

theorem valuation_dominates_order (δ : ℕ) (cost e : I → ℕ)
    (hc : ∀ i, δ ≤ cost i) : δ * order e ≤ value cost e := by
  rw [order, value, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right (e i) (hc i)

theorem order_le_one (δ h : ℕ) (cost e : I → ℕ)
    (hc : ∀ i, δ ≤ cost i) (hh : h ≤ δ) (hv : value cost e < δ+h) :
    order e ≤ 1 := by
  by_contra! hn
  have hs : δ*2 ≤ δ*order e := Nat.mul_le_mul_left δ hn
  have H := valuation_dominates_order δ cost e hc
  omega

theorem eq_zero_or_single (e : I → ℕ) (ho : order e ≤ 1) :
    (∀ i, e i = 0) ∨ ∃ i, e i = 1 ∧ ∀ j, j ≠ i → e j = 0 := by
  classical
  by_cases h : ∀ i, e i = 0
  · exact Or.inl h
  · push_neg at h
    obtain ⟨i,hi⟩ := h
    have htotal := Finset.sum_erase_add (Finset.univ : Finset I) e (Finset.mem_univ i)
    have hi1 : e i = 1 := by unfold order at ho; omega
    right
    refine ⟨i,hi1,?_⟩
    have hrem : (∑ j ∈ (Finset.univ : Finset I).erase i, e j) = 0 := by
      unfold order at ho
      omega
    intro j hj
    have H := Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _)
      (show j ∈ (Finset.univ : Finset I).erase i by simp [hj])
    omega

theorem singleton_value (δ : ℕ) (index e : I → ℕ)
    (i : I) (hi : e i = 1) (hj : ∀ j, j ≠ i → e j = 0) :
    value (fun j => δ+index j) e = δ+index i := by
  classical
  rw [value, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [hi, mul_one]
  · intro j _ h
    simp [hj j h]

/-- Every nonzero contributing exponent is one mode of index b<h, and
its digit cost is exactly T(h−b). This remains true with repeated indices
on distinct packets, arbitrary mode ordering, and a sub-menu. -/
theorem surviving_slot (δ h : ℕ) (index e : I → ℕ) (hh : h ≤ δ)
    (hv : value (fun j => δ+index j) e < δ+h) :
    (∀ i, e i = 0) ∨ ∃ i,
      e i = 1 ∧ (∀ j, j ≠ i → e j = 0) ∧ index i < h ∧
      PrecisionMenu.triangular (δ+h-value (fun j => δ+index j) e) =
        PrecisionMenu.triangular (h-index i) := by
  obtain h0 | ⟨i,hi,hother⟩ := eq_zero_or_single e
    (order_le_one δ h _ e (fun i => Nat.le_add_right δ (index i)) hh hv)
  · exact Or.inl h0
  · have he := singleton_value δ index e i hi hother
    rw [he] at hv
    refine Or.inr ⟨i, hi, hother, by omega, ?_⟩
    rw [he, show δ+h-(δ+index i)=h-index i by omega]

theorem initial_tetrahedral (h : ℕ) :
    6 * (∑ b ∈ Finset.range h, PrecisionMenu.triangular (h-b)) = h*(h+1)*(h+2) := by
  have hr (n : ℕ) :
      (∑ b ∈ Finset.range n, PrecisionMenu.triangular (n-b)) =
        ∑ b ∈ Finset.range n, PrecisionMenu.triangular (b+1) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro b hb
    obtain hb' := Finset.mem_range.mp hb
    congr 1
    omega
  rw [hr]
  induction h with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    have h := PrecisionMenu.two_mul_triangular (n+1)
    have hm : 6*PrecisionMenu.triangular (n+1) = 3*((n+1)*(n+1+1)) := by
      omega
    rw [hm]
    ring

/-- A coarse public cap on the physical number of modes of a fixed index.
It uses only one mode per tile of a packet, independently of probe count
and extension degree. State by cross multiplication to avoid floors. -/
theorem physical_mode_cap (M L D B packets modes : ℕ)
    (hP : packets*L ≤ 3*M) (hB : B*D = 2*L) (hm : modes ≤ packets*B) :
    modes*D ≤ 6*M := by
  calc
    modes*D ≤ (packets*B)*D := Nat.mul_le_mul_right D hm
    _ = packets*(B*D) := by ring
    _ = 2*(packets*L) := by rw [hB]; ring
    _ ≤ 6*M := by omega

/-- Exact pooled budget in the initial band. The zero tuple supplies the
base triangular term. Every contributing positive tuple is listed once,
even when several public modes have the same index. -/
theorem pooled_initial_band [DecidableEq I] (δ h : ℕ) (hpos : 0 < h) (hh : h ≤ δ) (index : I → ℕ) :
    (∑ b : I → Fin (δ+h),
      PrecisionMenu.triangular (δ+h-value (fun j => δ+index j) (fun j => (b j).val))) =
      PrecisionMenu.triangular (δ+h) +
        ∑ i ∈ Finset.univ.filter (fun i => index i < h),
          PrecisionMenu.triangular (h-index i) := by
  classical
  let zero : I → Fin (δ+h) := fun _ => ⟨0,by omega⟩
  let unit (i : I) : I → Fin (δ+h) := fun j =>
    if j=i then ⟨1,by omega⟩ else zero j
  let good := (Finset.univ : Finset I).filter fun i => index i < h
  let price (b : I → Fin (δ+h)) :=
    PrecisionMenu.triangular (δ+h-value (fun j => δ+index j) (fun j => (b j).val))
  let live (b : I → Fin (δ+h)) : Prop :=
    value (fun j => δ+index j) (fun j => (b j).val) < δ+h
  have he (i : I) : value (fun j => δ+index j) (fun j => (unit i j).val) = δ+index i := by
    apply singleton_value δ index _ i
    · simp [unit]
    · intro j hj
      simp [unit, hj, zero]
  have hz : value (fun j => δ+index j) (fun j => (zero j).val) = 0 := by simp [zero, value]
  have hs :
      (Finset.univ.filter live) = insert zero (good.image unit) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro hb
      obtain h0 | ⟨i,hi,ho,hit,_⟩ :=
        surviving_slot δ h index (fun j => (b j).val) hh hb
      · left
        funext j
        exact Fin.ext (h0 j)
      · right
        refine ⟨i, by simp [good, hit], ?_⟩
        funext j
        by_cases hj : j=i
        · subst j
          apply Fin.ext
          simp [unit, hi]
        · apply Fin.ext
          simp [unit, hj, zero, ho j hj]
    · rintro (rfl | ⟨i,hi,rfl⟩)
      · simp [live, hz, show 0 < δ+h by omega]
      · have hit := (Finset.mem_filter.mp hi).2
        change value (fun j => δ+index j) (fun j => (unit i j).val) < δ+h
        rw [he]
        omega
  have hni : zero ∉ good.image unit := by
    intro h'
    obtain ⟨i,_,e⟩ := Finset.mem_image.mp h'
    have eq := congrArg (fun f : I → Fin (δ+h) => (f i).val) e
    simp [unit, zero] at eq
  have hinj : Set.InjOn unit ↑good := by
    intro i _ j _ e
    by_contra h'
    have eq := congrArg (fun f : I → Fin (δ+h) => (f i).val) e
    simp [unit, zero, h'] at eq
  change (∑ b, price b) =
    PrecisionMenu.triangular (δ+h)+∑ i ∈ good, PrecisionMenu.triangular (h-index i)
  calc
    _ = ∑ b ∈ Finset.univ.filter live, price b := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro b _ hb
      have ho : δ+h ≤ value (fun j => δ+index j) (fun j => (b j).val) := by
        have h' : ¬ live b := by simpa using hb
        exact le_of_not_gt h'
      simp [price, Nat.sub_eq_zero_of_le ho, PrecisionMenu.triangular]
    _ = _ := by
      rw [hs, Finset.sum_insert hni, Finset.sum_image hinj]
      simp only [price, hz, Nat.sub_zero, he]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [show δ+h-(δ+index i)=h-index i by omega]

theorem group_by_index (h : ℕ) (index : I → ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i => index i < h), PrecisionMenu.triangular (h-index i)) =
      ∑ b ∈ Finset.range h,
        ((Finset.univ : Finset I).filter (fun i => index i = b)).card *
          PrecisionMenu.triangular (h-b) := by
  classical
  have expand (i : I) :
      (if index i < h then PrecisionMenu.triangular (h-index i) else 0) =
        ∑ b ∈ Finset.range h,
          if index i = b then PrecisionMenu.triangular (h-b) else 0 := by
    by_cases hh : index i < h
    · rw [if_pos hh, Finset.sum_eq_single_of_mem (index i) (Finset.mem_range.mpr hh)]
      · simp
      · intro b _ hb
        exact if_neg (Ne.symm hb)
    · rw [if_neg hh]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      apply if_neg
      intro e
      subst b
      exact hh (Finset.mem_range.mp hb)
  rw [Finset.sum_filter, Finset.sum_congr rfl (fun i _ => expand i), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The stated first-band pooled cap after clearing the positive public
denominator D_i. Index counts concern actual modes, not residues. -/
theorem pooled_index_bound [DecidableEq I] (δ h M D : ℕ) (hpos : 0 < h)
    (hh : h ≤ δ) (index : I → ℕ)
    (hc : ∀ b < h, ((Finset.univ : Finset I).filter (fun i => index i = b)).card*D ≤ 6*M) :
    (∑ t : I → Fin (δ+h), PrecisionMenu.triangular
      (δ+h-value (fun j => δ+index j) (fun j => (t j).val))) * D ≤
      PrecisionMenu.triangular (δ+h)*D + M*(h*(h+1)*(h+2)) := by
  classical
  rw [pooled_initial_band δ h hpos hh, group_by_index h index, add_mul]
  apply Nat.add_le_add_left
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ b ∈ Finset.range h, (6*M)*PrecisionMenu.triangular (h-b) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [mul_right_comm]
      exact Nat.mul_le_mul_right _ (hc b (Finset.mem_range.mp hb))
    _ = _ := by
      rw [← Finset.mul_sum, ← initial_tetrahedral h]
      ring

#print axioms group_by_index
#print axioms pooled_index_bound
#print axioms pooled_initial_band
#print axioms valuation_dominates_order
#print axioms eq_zero_or_single
#print axioms surviving_slot
#print axioms initial_tetrahedral
#print axioms physical_mode_cap

end P4InitialBand