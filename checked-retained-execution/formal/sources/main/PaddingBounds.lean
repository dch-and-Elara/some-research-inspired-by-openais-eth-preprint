import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Mathlib.Tactic

open scoped BigOperators

namespace PaddingBounds

/-- The native collision objective of the ordered-cell assignment. -/
noncomputable def collision {C : Type*} (cells : Finset C) (load : C → ℕ) (M : ℕ) : ℝ :=
  ∑ c ∈ cells, ((load c : ℝ) - (M : ℝ) / cells.card)^2

theorem cell_load_le_of_collision {C : Type*} (cells : Finset C) (load : C → ℕ)
    (M Delta : ℕ) (h : collision cells load M ≤ 2 * (M : ℝ) * Delta)
    {c : C} (hc : c ∈ cells) :
    (load c : ℝ) ≤ (M : ℝ) / cells.card + Real.sqrt (2 * (M : ℝ) * Delta) := by
  classical
  let mu : ℝ := (M : ℝ) / cells.card
  have hsq : ((load c : ℝ) - mu)^2 ≤ collision cells load M := by
    exact Finset.single_le_sum (fun i _ => sq_nonneg ((load i : ℝ) - mu)) hc
  have habs : |(load c : ℝ) - mu| ≤ Real.sqrt (2 * (M : ℝ) * Delta) := by
    apply (Real.le_sqrt (abs_nonneg _) (by positivity)).2
    simpa only [sq_abs] using hsq.trans h
  have hd := (le_abs_self ((load c : ℝ) - mu)).trans habs
  change (load c : ℝ) ≤ mu + _ 
  linarith

/-- Common padding rounds the maximum cell load up to the packet length. -/
def blocks (m L : ℕ) : ℕ := m / L + if m % L = 0 then 0 else 1

def paddedLoad (m L : ℕ) : ℕ := blocks m L * L

theorem paddedLoad_spec (m L : ℕ) (hL : 0 < L) :
    m ≤ paddedLoad m L ∧ paddedLoad m L < m + L ∧ L ∣ paddedLoad m L := by
  have hEq : m % L + m / L * L = m := by
    simpa only [Nat.mul_comm (m / L) L] using Nat.mod_add_div m L
  have hRem := Nat.mod_lt m hL
  refine ⟨?_, ?_, ⟨blocks m L, Nat.mul_comm _ _⟩⟩
  · by_cases hm : m % L = 0
    · simp [paddedLoad, blocks, hm]
      omega
    · simp [paddedLoad, blocks, hm, Nat.add_mul]
      omega
  · by_cases hm : m % L = 0
    · simp [paddedLoad, blocks, hm]
      omega
    · simp [paddedLoad, blocks, hm, Nat.add_mul]
      omega

/-- Number of common padded blocks over every ordered cell. -/
def packetCount {C : Type*} (cells : Finset C) (load : C → ℕ) (L : ℕ) : ℕ :=
  cells.card * blocks (cells.sup load) L

/-- Deterministic numerical assertion P8, without an asymptotic hypothesis:
P is computed by rounding the real maximum load, not assumed in the conclusion. -/
theorem p8_collision_padding {C : Type*} (cells : Finset C) (load : C → ℕ)
    (M Delta L : ℕ) (hL : 0 < L) (hCells : 0 < cells.card)
    (hMass : ∑ c ∈ cells, load c = M)
    (hColl : collision cells load M ≤ 2 * (M : ℝ) * Delta) :
    M ≤ packetCount cells load L * L ∧
      (packetCount cells load L : ℝ) * L - M ≤
        (cells.card : ℝ) * (Real.sqrt (2 * (M : ℝ) * Delta) + L) := by
  let peak := cells.sup load
  let H := paddedLoad peak L
  let S : ℝ := Real.sqrt (2 * (M : ℝ) * Delta)
  let mu : ℝ := (M : ℝ) / cells.card
  have hD : 0 < (cells.card : ℝ) := by exact_mod_cast hCells
  have hnon : 0 ≤ mu + S := by dsimp [mu, S]; positivity
  have hPeak : (peak : ℝ) ≤ mu + S := by
    have hm : peak ≤ ⌊mu+S⌋₊ := Finset.sup_le fun c hc =>
      Nat.le_floor (cell_load_le_of_collision cells load M Delta hColl hc)
    exact (Nat.cast_le.mpr hm).trans (Nat.floor_le hnon)
  have hRound := paddedLoad_spec peak L hL
  have hPH : packetCount cells load L * L = cells.card * H := by
    simp only [packetCount, H, peak, paddedLoad, Nat.mul_assoc]
  constructor
  · calc
      M = ∑ c ∈ cells, load c := hMass.symm
      _ ≤ ∑ _c ∈ cells, H := Finset.sum_le_sum fun c hc =>
        (Finset.le_sup hc).trans hRound.1
      _ = packetCount cells load L * L := by
        rw [hPH]
        simp
  · have hr : (H : ℝ) ≤ (peak : ℝ) + L := by
      exact_mod_cast hRound.2.1.le
    have ht : (H : ℝ) ≤ mu + (S + L) := by linarith
    have hPH' : (packetCount cells load L : ℝ) * L = cells.card * (H : ℝ) := by
      exact_mod_cast hPH
    have hmu : (cells.card : ℝ) * mu = M := by
      dsimp [mu]
      field_simp [hD.ne']
    rw [hPH']
    have ha := mul_le_mul_of_nonneg_left ht hD.le
    rw [mul_add, hmu] at ha
    change (cells.card : ℝ) * (H : ℝ) - (M : ℝ) ≤ (cells.card : ℝ) * (S + L)
    linarith

/-- At base palette size 64 the ordered-cell array is L^12. -/
theorem array_card_at_sixtyfour (a : ℕ) :
    (64 : ℕ)^(2*a) = (2^a)^12 := by
  calc
    (64 : ℕ)^(2*a) = (2^6)^(2*a) := by norm_num
    _ = (2 : ℕ)^(6*(2*a)) := (Nat.pow_mul 2 6 (2*a)).symm
    _ = (2^a)^12 := by rw [← Nat.pow_mul 2 a 12]; congr 1; omega

abbrev Slot (P : Type*) (L : ℕ) := P × Fin L

def slots {P : Type*} [DecidableEq P] (packets : Finset P) (L : ℕ) :
    Finset (Slot P L) := packets.product Finset.univ

def realSlots {P : Type*} [DecidableEq P] {L : ℕ} (packets : Finset P)
    (real : Slot P L → Bool) : Finset (Slot P L) :=
  (slots packets L).filter fun p => real p = true

def holes {P : Type*} [DecidableEq P] {L : ℕ} (packets : Finset P)
    (real : Slot P L → Bool) : Finset (Slot P L) :=
  (slots packets L).filter fun p => ¬ real p = true

def matched {P : Type*} [DecidableEq P] {L : ℕ} (packets : Finset P)
    (real : Slot P L → Bool) (t : ℤ) : Finset (Slot P L) :=
  (realSlots packets real).filter fun p =>
    ∃ x : Fin L, real (p.1,x) = true ∧ (x.val : ℤ) + t = (p.2.val : ℤ)

theorem mem_realSlots {P : Type*} [DecidableEq P] {L : ℕ} (packets : Finset P)
    (real : Slot P L → Bool) (p : Slot P L) :
    p ∈ realSlots packets real ↔ p.1 ∈ packets ∧ real p = true := by
  simp [realSlots, slots]

theorem mem_holes {P : Type*} [DecidableEq P] {L : ℕ} (packets : Finset P)
    (real : Slot P L → Bool) (p : Slot P L) :
    p ∈ holes packets real ↔ p.1 ∈ packets ∧ ¬ real p = true := by
  simp [holes, slots]

theorem real_add_holes {P : Type*} [DecidableEq P] {L : ℕ} (packets : Finset P)
    (real : Slot P L → Bool) :
    (realSlots packets real).card + (holes packets real).card = packets.card * L := by
  unfold realSlots holes
  rw [Finset.filter_card_add_filter_neg_card_eq_card]
  simp [slots]

/-- Each real shifted column maps injectively to its packet and to an index
in a window of length L-|t|; for positive t shift the index down by |t|. -/
theorem matched_card_le_clipped {P : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (real : Slot P L → Bool) (t : ℤ) :
    (matched packets real t).card ≤ packets.card * (L - t.natAbs) := by
  let f : Slot P L → P × ℕ := fun p =>
    (p.1, if 0 ≤ t then p.2.val - t.natAbs else p.2.val)
  have hwin : ∀ y ∈ matched packets real t, y.1 ∈ packets ∧
      (0 ≤ t → t.natAbs ≤ y.2.val) ∧
      (f y).2 < L - t.natAbs := by
    intro y hy
    obtain ⟨hyR, x, _, hx⟩ := Finset.mem_filter.mp hy
    have hi := x.isLt
    have hj := y.2.isLt
    refine ⟨((mem_realSlots packets real y).mp hyR).1, ?_, ?_⟩
    · intro hn
      have ha := Int.natAbs_of_nonneg hn
      omega
    · dsimp [f]
      split <;> rename_i h
      · have ha := Int.natAbs_of_nonneg h
        omega
      · have ha : (t.natAbs : ℤ) = -t := by
          simpa using Int.natAbs_of_nonneg (show 0 ≤ -t by omega)
        omega
  rw [← Finset.card_range (L - t.natAbs), ← Finset.card_product]
  apply Finset.card_le_card_of_injOn f
  · intro y hy
    have h := hwin y hy
    exact Finset.mem_product.mpr ⟨h.1, Finset.mem_range.mpr h.2.2⟩
  · intro y hy z hz h
    have h1 := congrArg (fun p : P × ℕ => p.1) h
    change y.1 = z.1 at h1
    apply Prod.ext h1
    apply Fin.ext
    have h' := congrArg Prod.snd h
    by_cases ht : 0 ≤ t
    · have hy' := (hwin y hy).2.1 ht
      have hz' := (hwin z hz).2.1 ht
      simp [f, ht] at h'
      omega
    · simpa [f, ht] using h'

/-- Equality vertices with no incoming real partial shift. -/
def untouched {A V : Type*} [DecidableEq V] (old : Finset V) (owner : A → V)
    (hit : Finset A) : Finset V := old \ hit.image owner

theorem old_le_untouched_add_matched {A V : Type*} [DecidableEq V] (old : Finset V)
    (owner : A → V) (hit : Finset A) :
    old.card ≤ (untouched old owner hit).card + hit.card := by
  have he := Finset.card_sdiff_add_card_inter old (hit.image owner)
  have hm : (old ∩ hit.image owner).card ≤ hit.card :=
    (Finset.card_le_card (fun _ h => (Finset.mem_inter.mp h).2)).trans Finset.card_image_le
  unfold untouched
  omega

/-- Exact finite outer-grid lower bound: theta is the certified equality-to-wire
ratio. Choose theta=1/6, or 1/2 if subdivisions are columns. -/
theorem outer_grid_bound {P V : Type*} [DecidableEq P] [DecidableEq V] {L : ℕ}
    (packets : Finset P) (real : Slot P L → Bool) (t : ℤ)
    (old : Finset V) (owner : Slot P L → V)
    (theta c : ℝ) (hc : c ≤ theta)
    (hEqual : theta * ((realSlots packets real).card : ℝ) ≤ (old.card : ℝ))
    (hT : (1 - theta + c) * (L : ℝ) ≤ t.natAbs) :
    c * ((realSlots packets real).card : ℝ) -
        (theta - c) * ((holes packets real).card : ℝ) ≤
      ((untouched old owner (matched packets real t)).card : ℝ) := by
  let M := (realSlots packets real).card
  let G := (holes packets real).card
  let K := (untouched old owner (matched packets real t)).card
  have hCard : (old.card : ℝ) ≤ K + (packets.card : ℝ) * ((L - t.natAbs : ℕ) : ℝ) := by
    have hn := (old_le_untouched_add_matched old owner (matched packets real t)).trans
      (Nat.add_le_add_left (matched_card_le_clipped packets real t) _)
    exact_mod_cast hn
  have hMass : (M : ℝ) + G = (packets.card : ℝ) * L := by
    exact_mod_cast real_add_holes packets real
  have hWin : ((L - t.natAbs : ℕ) : ℝ) ≤ (theta - c) * (L : ℝ) := by
    by_cases hh : t.natAbs ≤ L
    · rw [Nat.cast_sub hh]
      linarith
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hh), Nat.cast_zero]
      exact mul_nonneg (sub_nonneg.mpr hc) (Nat.cast_nonneg L)
  have he := hEqual.trans (hCard.trans
    (add_le_add_left (mul_le_mul_of_nonneg_left hWin (Nat.cast_nonneg _)) _))
  change c * (M : ℝ) - (theta - c) * (G : ℝ) ≤ K
  have ha : (packets.card : ℝ) * ((theta-c) * L) = (theta-c) * ((M : ℝ) + G) := by
    rw [hMass]
    ring
  rw [ha] at he
  change theta * (M : ℝ) ≤ (K : ℝ) + (theta-c) * ((M : ℝ) + G) at he
  linarith


/-- For a physical packing counted by the common cell blocks, the number
of actual dummy slots is exactly the padding slack used by P8. -/
theorem physical_holes_le_collision {P C : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (real : Slot P L → Bool)
    (cells : Finset C) (load : C → ℕ) (Delta : ℕ)
    (hL : 0 < L) (hCells : 0 < cells.card)
    (hMass : ∑ c ∈ cells, load c = (realSlots packets real).card)
    (hPack : packets.card = packetCount cells load L)
    (hColl : collision cells load (realSlots packets real).card ≤
        2 * ((realSlots packets real).card : ℝ) * Delta) :
    ((holes packets real).card : ℝ) ≤
      (cells.card : ℝ) *
        (Real.sqrt (2 * ((realSlots packets real).card : ℝ) * Delta) + L) := by
  have hm : ((realSlots packets real).card : ℝ) + ((holes packets real).card : ℝ) =
      (packets.card : ℝ) * (L : ℝ) := by
    exact_mod_cast real_add_holes packets real
  have hb := (p8_collision_padding cells load (realSlots packets real).card
    Delta L hL hCells hMass hColl).2
  rw [hPack] at hm
  linarith

/-- The explicit collision correction to the outer-grid lower bound. -/
theorem p8_outer_grid {P C V : Type*} [DecidableEq P] [DecidableEq V] {L : ℕ}
    (packets : Finset P) (real : Slot P L → Bool)
    (cells : Finset C) (load : C → ℕ) (Delta : ℕ)
    (hL : 0 < L) (hCells : 0 < cells.card)
    (hMass : ∑ c ∈ cells, load c = (realSlots packets real).card)
    (hPack : packets.card = packetCount cells load L)
    (hColl : collision cells load (realSlots packets real).card ≤
        2 * ((realSlots packets real).card : ℝ) * Delta)
    (t : ℤ) (old : Finset V) (owner : Slot P L → V)
    (theta c : ℝ) (hc : c ≤ theta)
    (hEqual : theta * ((realSlots packets real).card : ℝ) ≤ (old.card : ℝ))
    (hT : (1 - theta + c) * (L : ℝ) ≤ t.natAbs) :
    c * ((realSlots packets real).card : ℝ) -
        (theta - c) * ((cells.card : ℝ) *
          (Real.sqrt (2 * ((realSlots packets real).card : ℝ) * Delta) + L)) ≤
      ((untouched old owner (matched packets real t)).card : ℝ) := by
  apply le_trans _ (outer_grid_bound packets real t old owner theta c hc hEqual hT)
  apply sub_le_sub_left
  exact mul_le_mul_of_nonneg_left
    (physical_holes_le_collision packets real cells load Delta hL hCells hMass hPack hColl)
    (sub_nonneg.mpr hc)

def unitShift (negative : Bool) : ℤ := if negative then -1 else 1

def endSeat {L : ℕ} (negative : Bool) (y : Fin L) : Bool :=
  if negative then decide (y.val = L - 1) else decide (y.val = 0)

def adjacentIndex {L : ℕ} (negative : Bool) (y : Fin L) : Fin L :=
  if negative then
    if h : y.val + 1 < L then ⟨y.val + 1, h⟩ else y
  else ⟨y.val - 1, (Nat.sub_le _ _).trans_lt y.isLt⟩

theorem endSeat_index {L : ℕ} (negative : Bool) (y : Fin L)
    (h : endSeat negative y = true) :
    y.val = if negative then L - 1 else 0 := by
  cases negative <;> simpa [endSeat] using h

/-- Every nonboundary column has exactly the adjacent candidate predecessor. -/
theorem adjacent_reaches {L : ℕ} (negative : Bool) (y : Fin L)
    (hy : endSeat negative y ≠ true) :
    ((adjacentIndex negative y).val : ℤ) + unitShift negative = (y.val : ℤ) := by
  have hL := y.isLt
  cases negative
  · simp [endSeat] at hy
    simp [adjacentIndex, unitShift]
    omega
  · simp [endSeat] at hy
    have h : y.val + 1 < L := by omega
    simp [adjacentIndex, unitShift, h]

def unmatched {P : Type*} [DecidableEq P] {L : ℕ} (packets : Finset P)
    (real : Slot P L → Bool) (t : ℤ) : Finset (Slot P L) :=
  realSlots packets real \ matched packets real t

/-- An unmatched real column at either unit shift charges an end seat
or a genuine padding hole. The predecessor charge is injective. -/
theorem unmatched_unit_le_endpoints_add_holes {P : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (real : Slot P L → Bool) (negative : Bool) :
    (unmatched packets real (unitShift negative)).card ≤
      packets.card + (holes packets real).card := by
  let U := unmatched packets real (unitShift negative)
  let isEnd : Slot P L → Prop := fun p => endSeat negative p.2 = true
  letI : DecidablePred isEnd := fun p => inferInstanceAs (Decidable (endSeat negative p.2 = true))
  let E := U.filter isEnd
  let I := U.filter fun p => ¬ isEnd p
  have hSum : E.card + I.card = U.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (s := U) isEnd
  have hEnd : E.card ≤ packets.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      have hu : p ∈ U := (Finset.mem_filter.mp hp).1
      have hr : p ∈ realSlots packets real := (Finset.mem_sdiff.mp hu).1
      exact ((mem_realSlots packets real p).mp hr).1
    · intro y hy z hz h
      apply Prod.ext h
      apply Fin.ext
      exact (endSeat_index negative y.2 (Finset.mem_filter.mp hy).2).trans
        (endSeat_index negative z.2 (Finset.mem_filter.mp hz).2).symm
  have hInterior : I.card ≤ (holes packets real).card := by
    let f : Slot P L → Slot P L := fun p => (p.1, adjacentIndex negative p.2)
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      have hu : p ∈ U := (Finset.mem_filter.mp hp).1
      obtain ⟨hreal, hmiss⟩ := Finset.mem_sdiff.mp hu
      have hPacket := ((mem_realSlots packets real p).mp hreal).1
      apply (mem_holes packets real (f p)).mpr
      refine ⟨hPacket, ?_⟩
      intro hPred
      apply hmiss
      apply Finset.mem_filter.mpr
      exact ⟨hreal, adjacentIndex negative p.2, hPred,
        adjacent_reaches negative p.2 (Finset.mem_filter.mp hp).2⟩
    · intro y hy z hz h
      have h1 := congrArg (fun p : Slot P L => p.1) h
      change y.1 = z.1 at h1
      apply Prod.ext h1
      apply Fin.ext
      have hd := congrArg (fun p : Slot P L => p.2.val) h
      change (adjacentIndex negative y.2).val = (adjacentIndex negative z.2).val at hd
      have hY := adjacent_reaches negative y.2 (Finset.mem_filter.mp hy).2
      have hZ := adjacent_reaches negative z.2 (Finset.mem_filter.mp hz).2
      omega
  change U.card ≤ packets.card + (holes packets real).card
  omega

/-- Finite endpoint optimality for binary equalities in P9. Each original
equality owns its two distinct real ports. Every untouched one charges both
ports to the preceding bound; the owners prevent two equalities sharing a port. -/
theorem binary_untouched_unit_bound {P V : Type*} [DecidableEq P] [DecidableEq V]
    {L : ℕ} (packets : Finset P) (real : Slot P L → Bool)
    (negative : Bool) (old : Finset V) (owner : Slot P L → V)
    (port : V → Bool → Slot P L)
    (hReal : ∀ v ∈ old, ∀ b, port v b ∈ realSlots packets real)
    (hOwner : ∀ v ∈ old, ∀ b, owner (port v b) = v)
    (hDistinct : ∀ v ∈ old, port v false ≠ port v true) :
    2 * (untouched old owner (matched packets real (unitShift negative))).card ≤
      packets.card + (holes packets real).card := by
  let T := matched packets real (unitShift negative)
  let K := untouched old owner T
  have hK : K ⊆ old := Finset.sdiff_subset
  have ht : (K.product (Finset.univ : Finset Bool)).card ≤
      (unmatched packets real (unitShift negative)).card := by
    apply Finset.card_le_card_of_injOn (fun q : V × Bool => port q.1 q.2)
    · intro q hq
      have hq1 : q.1 ∈ K := (Finset.mem_product.mp hq).1
      have hOld : q.1 ∈ old := hK hq1
      apply Finset.mem_sdiff.mpr
      refine ⟨hReal q.1 hOld q.2, ?_⟩
      intro hm
      exact (Finset.mem_sdiff.mp hq1).2
        (Finset.mem_image.mpr ⟨port q.1 q.2, hm, hOwner q.1 hOld q.2⟩)
    · rintro ⟨v,b⟩ hp ⟨w,d⟩ hq he
      have hv : v ∈ old := hK (Finset.mem_product.mp hp).1
      have hw : w ∈ old := hK (Finset.mem_product.mp hq).1
      have hvw : v = w :=
        ((hOwner v hv b).symm.trans (congrArg owner he)).trans (hOwner w hw d)
      subst w
      have hb : b = d := by
        cases b <;> cases d
        · rfl
        · exact False.elim (hDistinct v hv he)
        · exact False.elim (hDistinct v hv he.symm)
        · rfl
      exact Prod.ext rfl hb
  have h := ht.trans (unmatched_unit_le_endpoints_add_holes packets real negative)
  have hb : (Finset.univ : Finset Bool).card = 2 := by decide
  have hc : (K.product (Finset.univ : Finset Bool)).card = K.card * 2 := by
    calc
      _ = K.card * (Finset.univ : Finset Bool).card := Finset.card_product _ _
      _ = _ := by rw [hb]
  rw [hc] at h
  change 2 * K.card ≤ _
  omega

/-- The finite leading-constant upper bound stated with the actual count
of real wires, rather than a separately supplied number of holes. -/
theorem binary_untouched_unit_mass {P V : Type*} [DecidableEq P] [DecidableEq V]
    {L : ℕ} (packets : Finset P) (real : Slot P L → Bool)
    (negative : Bool) (old : Finset V) (owner : Slot P L → V)
    (port : V → Bool → Slot P L)
    (hReal : ∀ v ∈ old, ∀ b, port v b ∈ realSlots packets real)
    (hOwner : ∀ v ∈ old, ∀ b, owner (port v b) = v)
    (hDistinct : ∀ v ∈ old, port v false ≠ port v true) :
    2 * (untouched old owner (matched packets real (unitShift negative))).card ≤
      packets.card + (packets.card * L - (realSlots packets real).card) := by
  have he := real_add_holes packets real
  have hb := binary_untouched_unit_bound packets real negative old owner port hReal hOwner hDistinct
  omega

#print axioms p8_collision_padding
#print axioms physical_holes_le_collision
#print axioms p8_outer_grid
#print axioms unmatched_unit_le_endpoints_add_holes
#print axioms binary_untouched_unit_bound
#print axioms binary_untouched_unit_mass
#print axioms matched_card_le_clipped
#print axioms outer_grid_bound

end PaddingBounds
