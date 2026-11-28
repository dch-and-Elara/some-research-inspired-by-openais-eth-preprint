import ReceiverOrderPotential
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Push

open scoped BigOperators

namespace Reconstruction.ColorAlphabet

noncomputable section

variable {T : Type*} {A : T → Type*} [Fintype T] [DecidableEq T]
  [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)]

private def remainingReceivers (S : Remaining A) : Finset (Receiver A) :=
  Finset.univ.filter fun x => x.2 ∈ S x.1

@[simp] private theorem mem_remaining (S : Remaining A) (x : Receiver A) :
    x ∈ remainingReceivers S ↔ x.2 ∈ S x.1 := by simp [remainingReceivers]

private theorem receivers_remove (S : Remaining A) (x : Receiver A) :
    remainingReceivers (removeLetter S x) = (remainingReceivers S).erase x := by
  rcases x with ⟨t,b⟩
  ext y
  rcases y with ⟨u,c⟩
  by_cases h : u = t
  · subst u
    simp [removeLetter]
  · simp [removeLetter, Function.update_of_ne h, h]

private def Exhausts (S : Remaining A) (xs : List (Receiver A)) : Prop :=
  xs.Nodup ∧ ∀ x : Receiver A, x ∈ xs ↔ x ∈ remainingReceivers S

/-- At each step the chosen receiver lies in a coordinate of maximum remaining size. -/
def LargestFirst : Remaining A → List (Receiver A) → Prop
  | _, [] => True
  | S, x :: xs => (∀ t, (S t).card ≤ (S x.1).card) ∧ LargestFirst (removeLetter S x) xs

private theorem exhausts_cons (S : Remaining A) (x : Receiver A) (xs : List (Receiver A)) :
    Exhausts S (x :: xs) ↔ x ∈ remainingReceivers S ∧ Exhausts (removeLetter S x) xs := by
  classical
  constructor
  · intro h
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp h.1
    refine ⟨(h.2 x).mp List.mem_cons_self, hxs, fun y => ?_⟩
    rw [receivers_remove, Finset.mem_erase, ← h.2 y, List.mem_cons]
    by_cases e : y = x
    · subst y; simp [hx]
    · simp [e]
  · rintro ⟨hx, htail⟩
    have hnx : x ∉ xs := by simpa [htail.2 x, receivers_remove]
    refine ⟨List.nodup_cons.mpr ⟨hnx, htail.1⟩, fun y => ?_⟩
    rw [List.mem_cons, htail.2 y, receivers_remove, Finset.mem_erase]
    by_cases hy : y = x
    · subst y; simp [hx]
    · simp [hy]

private theorem counts_remove (S : Remaining A) (x : Receiver A) (hx : x.2 ∈ S x.1) :
    (fun t => (removeLetter S x t).card) =
      Function.update (fun t => (S t).card) x.1 ((S x.1).card - 1) := by
  funext t
  by_cases h : t = x.1
  · subst t; simp [removeLetter, Finset.card_erase_of_mem hx]
  · simp [removeLetter, Function.update_of_ne h]

private theorem order_score (S : Remaining A) (xs : List (Receiver A)) (hex : Exhausts S xs)
    (m : ℕ) (hm : ∀ i, (S i).card ≤ m) :
    ((selectedWithin S xs).card : ℚ) ≤ orderPotential (fun t => (S t).card) m ∧
      (LargestFirst S xs →
        ((selectedWithin S xs).card : ℚ) = orderPotential (fun t => (S t).card) m) := by
  induction xs generalizing S with
  | nil =>
    have hz (i : T) : (S i).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      exact List.not_mem_nil ((hex.2 ⟨i,c⟩).mpr ((mem_remaining ..).mpr hc))
    have hv (j : ℕ) : clippedVolume (fun t => (S t).card) (j+1) =
        clippedVolume (fun t => (S t).card) j := by simp [clippedVolume, hz]
    rw [potential_sum]
    have he : selectedWithin S [] = ∅ := by ext v; simp [SelectedBy]
    simp [he, hv]
  | cons x xs ih =>
    obtain ⟨hx, htail⟩ := (exhausts_cons S x xs).mp hex
    have hx' := (mem_remaining ..).mp hx
    have hcard := Finset.card_pos.mpr ⟨x.2, hx'⟩
    have hb : ∀ i, (removeLetter S x i).card ≤ m := by
      intro i
      rw [congrFun (counts_remove S x hx') i]
      by_cases h : i = x.1
      · subst i; simp only [Function.update_self]; exact (Nat.sub_le _ _).trans (hm _)
      · simpa [Function.update_of_ne h] using hm i
    have hn := ih (removeLetter S x) htail hb
    have hg := greedy_gain (fun t => (S t).card) x.1 hcard m hm
    rw [selectedWithin_card_gain S x xs hx']
    push_cast [Nat.cast_sub (Nat.succ_le_of_lt hcard)]
    rw [counts_remove S x hx'] at hn
    refine ⟨by linarith only [hg.1, hn.1], fun h => ?_⟩
    have hm' := hg.2 h.1
    have ht' := hn.2 h.2
    linarith only [hm', ht']

private theorem greedy_exists (S : Remaining A) :
    ∃ xs : List (Receiver A), Exhausts S xs ∧ LargestFirst S xs := by
  classical
  have h : ∀ U : Finset (Receiver A), ∀ S : Remaining A,
      remainingReceivers S = U → ∃ xs : List (Receiver A), Exhausts S xs ∧ LargestFirst S xs := by
    intro U
    induction U using Finset.strongInductionOn
    rename_i U ih
    intro S hS
    by_cases hU : U.Nonempty
    · obtain ⟨someReceiver, hsome⟩ := hU
      have hst := (mem_remaining ..).mp (hS.symm ▸ hsome)
      have hT : (Finset.univ : Finset T).Nonempty := ⟨someReceiver.1, Finset.mem_univ _⟩
      obtain ⟨t, -, ht⟩ := (Finset.univ : Finset T).exists_max_image (fun t => (S t).card) hT
      have ht' (i : T) : (S i).card ≤ (S t).card := ht i (Finset.mem_univ _)
      have hspos : 0 < (S someReceiver.1).card := Finset.card_pos.mpr ⟨_, hst⟩
      obtain ⟨c, hc⟩ := Finset.card_pos.mp (hspos.trans_le (ht' _))
      let x : Receiver A := ⟨t,c⟩
      have hx : x ∈ remainingReceivers S := (mem_remaining ..).mpr hc
      have hxU : x ∈ U := hS ▸ hx
      have hlt : U.erase x ⊂ U := Finset.erase_ssubset hxU
      have he : remainingReceivers (removeLetter S x) = U.erase x := by rw [receivers_remove, hS]
      obtain ⟨xs, hex, hl⟩ := ih (U.erase x) hlt (removeLetter S x) he
      exact ⟨x :: xs, (exhausts_cons S x xs).mpr ⟨hx, hex⟩, ht', hl⟩
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hU
      exact ⟨[], ⟨by simp, fun x => by simp [hS, hempty]⟩, trivial⟩
  exact h _ S rfl

private theorem exhaustive_full (xs : List (Receiver A)) :
    Exhausts (fun _ => Finset.univ) xs ↔ CompleteOrder xs := by
  simp [Exhausts, CompleteOrder]

/-- Every labelled permutation is bounded by the clipped-volume formula.
Every complete order using the largest-remaining rule attains that value. -/
theorem complete_order_score (xs : List (Receiver A)) (hx : CompleteOrder xs)
    (m : ℕ) (hm : ∀ i : T, Fintype.card (A i) ≤ m) :
    ((selectedColumns xs).card : ℚ) ≤ orderPotential (fun i : T => Fintype.card (A i)) m ∧
      (LargestFirst (fun _ => Finset.univ) xs →
        ((selectedColumns xs).card : ℚ) = orderPotential (fun i : T => Fintype.card (A i)) m) := by
  simpa only [selectedWithin_univ, Finset.card_univ] using
    order_score _ xs ((exhaustive_full xs).mpr hx) m (by simpa using hm)

/-- The maximum over all labelled receiver permutations and the generalized independence
number both equal the finite clipped-volume score. -/
theorem receiver_order_maximum (m : ℕ) (hm : ∀ i : T, Fintype.card (A i) ≤ m) :
    IsGreatest {z : ℚ | ∃ xs : List (Receiver A), CompleteOrder xs ∧
      z = (selectedColumns xs).card}
      (orderPotential (fun i : T => Fintype.card (A i)) m) ∧
    IsGreatest {z : ℚ | ∃ S : Finset (Word A), GeneralizedIndependent S ∧ z = S.card}
      (orderPotential (fun i : T => Fintype.card (A i)) m) := by
  obtain ⟨xs, hex, hgreedy⟩ := greedy_exists (fun _ : T => Finset.univ (α := A _))
  have hcomplete := (exhaustive_full xs).mp hex
  have heq := (complete_order_score xs hcomplete m hm).2 hgreedy
  refine ⟨⟨⟨xs, hcomplete, heq.symm⟩, ?_⟩, ⟨⟨selectedColumns xs, ?_, heq.symm⟩, ?_⟩⟩
  · rintro z ⟨ys, hy, rfl⟩
    exact (complete_order_score ys hy m hm).1
  · exact generalizedIndependent_of_order (fun v hv => (mem_selectedColumns ..).mp hv)
  · rintro z ⟨S, hs, rfl⟩
    obtain ⟨ys, hy, hsub⟩ := (generalizedIndependent_iff_order S).mp hs
    have hc : (S.card : ℚ) ≤ (selectedColumns ys).card := by exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (complete_order_score ys hy m hm).1

/-- Proposition 2.1 for the heterogeneous alphabet sizes of the paper. -/
theorem heterogeneous_receiver_order (q : ℕ) (r : Fin q → ℕ) :
    let m := Finset.univ.sup r
    let z := ∑ j ∈ Finset.range m, rate (j+1) *
      ((∏ i, (((min (r i) (j+1)) : ℕ) : ℚ)^2) -
        (∏ i, (((min (r i) j) : ℕ) : ℚ)^2))
    IsGreatest {n : ℚ | ∃ xs : List (Receiver (fun i => Fin (r i))),
      CompleteOrder xs ∧ n = (selectedColumns xs).card} z ∧
    IsGreatest {n : ℚ | ∃ S : Finset (Word (fun i => Fin (r i))),
      GeneralizedIndependent S ∧ n = S.card} z := by
  have hm (i : Fin q) : Fintype.card (Fin (r i)) ≤ Finset.univ.sup r := by
    rw [Fintype.card_fin]
    exact Finset.le_sup (Finset.mem_univ i)
  simpa only [potential_sum, clippedVolume, Fintype.card_fin] using
    receiver_order_maximum (A := fun i => Fin (r i)) _ hm

end

end Reconstruction.ColorAlphabet
