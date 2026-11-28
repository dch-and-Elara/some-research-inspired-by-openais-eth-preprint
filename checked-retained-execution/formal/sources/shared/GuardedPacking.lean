import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

open scoped BigOperators

namespace GuardedPacking

/-- Loads count all ports at a cell, including both ports of one equality. -/
def cellLoad {E C : Type*} (w : E → C → ℕ) (s : Finset E) (c : C) : ℕ :=
  ∑ e ∈ s, w e c

/-- Integer overflow above the available seats, summed over all cells. -/
def overflow {E C : Type*} [Fintype C] (w : E → C → ℕ)
    (cap : C → ℕ) (s : Finset E) : ℕ :=
  ∑ c : C, (cellLoad w s c - cap c)

theorem cellLoad_mono {E C : Type*} {s t : Finset E} (h : t ⊆ s)
    (w : E → C → ℕ) (c : C) : cellLoad w t c ≤ cellLoad w s c := by
  unfold cellLoad
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)

/-- If a marked object meets an overfull cell, deleting it decreases
the total overflow by at least one, including when it uses two such seats. -/
theorem overflow_erase_lt {E C : Type*} [DecidableEq E] [Fintype C]
    (w : E → C → ℕ) (cap : C → ℕ) (s : Finset E) {e : E} (he : e ∈ s)
    {c : C} (hc : cap c < cellLoad w s c) (hw : 0 < w e c) :
    overflow w cap (s.erase e) < overflow w cap s := by
  classical
  have heq : cellLoad w (s.erase e) c + w e c = cellLoad w s c := by
    exact Finset.sum_erase_add s (fun e => w e c) he
  unfold overflow
  apply Finset.sum_lt_sum
  · intro j hj
    exact Nat.sub_le_sub_right (cellLoad_mono (Finset.erase_subset e s) w j) _
  · refine ⟨c, Finset.mem_univ _, ?_⟩
    omega

/-- Deterministic finite deletion bound in P9. It uses no probabilistic assumption,
and no assumption on a marked object's incidence multiplicities. -/
theorem keep_within_capacity {E C : Type*} [DecidableEq E] [Fintype C]
    (w : E → C → ℕ) (cap : C → ℕ) (s : Finset E) :
    ∃ t : Finset E, t ⊆ s ∧
      (∀ c, cellLoad w t c ≤ cap c) ∧
      s.card ≤ t.card + overflow w cap s := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases h : ∀ c, cellLoad w s c ≤ cap c
  · exact ⟨s, Finset.Subset.rfl, h, Nat.le_add_right _ _⟩
  · push_neg at h
    obtain ⟨c, hc⟩ := h
    have hE : ∃ e ∈ s, 0 < w e c := by
      by_contra hE
      push_neg at hE
      have hz : cellLoad w s c = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        exact Nat.eq_zero_of_le_zero (hE e he)
      omega
    obtain ⟨e, he, hw⟩ := hE
    obtain ⟨t, hts, htcap, htcard⟩ := ih (s.erase e) (Finset.erase_ssubset he)
    refine ⟨t, hts.trans (Finset.erase_subset e s), htcap, ?_⟩
    have hcard := Finset.card_erase_add_one he
    have hover := overflow_erase_lt w cap s he hc hw
    omega

/-- A left or right endpoint of a length-L packet. -/
def endpoint (L : ℕ) (right : Bool) : ℕ := if right then L - 1 else 0

/-- Endpoint slots are distinct in the source's packets. -/
theorem endpoints_ne {L : ℕ} (hL : 2 ≤ L) : endpoint L false ≠ endpoint L true := by
  simp [endpoint]
  omega

/-- The negative sign uses the right endpoint; the positive sign uses the left.
The proof forbids a predecessor in the whole packet, even before restricting to
real row ports, so applies to every physical packet with that slot. -/
theorem endpoint_no_predecessor {L : ℕ} (hL : 0 < L) (right : Bool)
    {t : ℤ} (ht : if right then t < 0 else 0 < t) :
    ∀ x : ℕ, x < L → (x : ℤ) + t ≠ (endpoint L right : ℤ) := by
  intro x hx
  cases right <;> simp [endpoint] at ht ⊢ <;> omega

/-- The two ports of every protected equality are unsupported.
No upper bound on the magnitude of the nonzero translation is needed. -/
theorem protected_eq_has_no_predecessor {E : Type*}
    (slot : E → Bool → ℕ) {L : ℕ} (hL : 0 < L)
    (right : Bool) {t : ℤ} (ht : if right then t < 0 else 0 < t)
    {e : E} (he : ∀ p, slot e p = endpoint L right) :
    ∀ p : Bool, ∀ x : ℕ, x < L → (x : ℤ) + t ≠ (slot e p : ℤ) := by
  intro p x hx
  rw [he p]
  exact endpoint_no_predecessor hL right ht x hx

/-- With orientation masks replicated exactly b times, an ordered cell has
exactly b left-endpoint seats and exactly b right-endpoint seats. The equal
coordinates of the packet type contribute no orientation bits and are omitted. -/
def endMask {I : Type*} (right : Bool) (m : I → Bool) : I → Bool :=
  fun i => if right then !m i else m i


/-- Physical coordinates of the two packet endpoints. -/
theorem endpoint_testBit (a i : ℕ) (hi : i < a) (right : Bool) :
    Nat.testBit (endpoint (2 ^ a) right) i = right := by
  cases right <;> simp [endpoint, hi]

/-- For each unequal coordinate the packet's binary orientation rule
has the endpoint's all-zero or all-one bit profile. -/
theorem endMask_at_physical_endpoint {I : Type*} (a : ℕ)
    (coord : I → Fin a) (right : Bool) (m : I → Bool) :
    (fun i => if Nat.testBit (endpoint (2 ^ a) right) (coord i).val then !m i else m i) =
      endMask right m := by
  funext i
  rw [endpoint_testBit a (coord i).val (coord i).isLt right]
  rfl

theorem endMask_involutive {I : Type*} (right : Bool) :
    Function.Involutive (endMask (I := I) right) := by
  intro m
  funext i
  cases right <;> simp [endMask]

/-- Replicas and endpoint seats for a fixed unordered packet type. -/
def endpointSeatsEquiv {I : Type*} (b : ℕ) (right : Bool) (c : I → Bool) :
    {p : (I → Bool) × Fin b // endMask right p.1 = c} ≃ Fin b where
  toFun p := p.1.2
  invFun k := ⟨(endMask right c, k), endMask_involutive right c⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (endMask_involutive right p.1.1).symm.trans (congrArg (endMask right) p.2)
        |>.symm
    · rfl
  right_inv _ := rfl

theorem card_endpointSeats {I : Type*} (b : ℕ) (right : Bool)
    (c : I → Bool) :
    Nat.card {p : (I → Bool) × Fin b // endMask right p.1 = c} = b := by
  simpa only [Nat.card_fin] using Nat.card_congr (endpointSeatsEquiv b right c)


/-- The two physical ports of a marked equality are named by a Boolean. -/
abbrev markedPort {E C : Type*} (label : E → Bool → C) (s : Finset E) (c : C) :=
  Σ e : {e // e ∈ s}, {p : Bool // label e.1 p = c}

/-- A double hit of a cell by one equality is counted twice. -/
def multiplicity {E C : Type*} [DecidableEq C] (label : E → Bool → C) (e : E)
    (c : C) : ℕ := Fintype.card {p : Bool // label e p = c}

theorem card_markedPort {E C : Type*} [DecidableEq C] (label : E → Bool → C)
    (s : Finset E) (c : C) :
    Fintype.card (markedPort label s c) = cellLoad (multiplicity label) s c := by
  classical
  unfold markedPort
  rw [Fintype.card_sigma]
  exact Finset.sum_attach s (fun e => multiplicity label e c)

/-- The cell capacity realizes injections of *whole equality ports* into
their own endpoint seats. Distinct marked objects need not have distinct labels. -/
theorem seat_markedPorts {E C I : Type*} [DecidableEq C] (label : E → Bool → C)
    (s : Finset E) (b : ℕ) (right : Bool) (c : C) (v : I → Bool)
    (h : cellLoad (multiplicity label) s c ≤ b) :
    Nonempty (markedPort label s c ↪ {p : (I → Bool) × Fin b // endMask right p.1 = v}) := by
  classical
  rw [← card_markedPort] at h
  exact ⟨((Fintype.equivFin (markedPort label s c)).toEmbedding.trans
    (Fin.castLEEmb h)).trans (endpointSeatsEquiv b right v).symm.toEmbedding⟩

/-- The deterministic overshoot paid by deletion obeys Cauchy--Schwarz.
The means need only be bounded above by the cell capacities. -/
theorem overflow_sq_le {E C : Type*} [Fintype C]
    (w : E → C → ℕ) (cap : C → ℕ) (s : Finset E)
    (μ : C → ℝ) (hc : ∀ c, μ c ≤ (cap c : ℝ)) :
    (overflow w cap s : ℝ)^2 ≤
      (Fintype.card C : ℝ) * ∑ c, ((cellLoad w s c : ℝ) - μ c)^2 := by
  classical
  have hpoint : ∀ c : C, ((cellLoad w s c - cap c : ℕ) : ℝ) ≤
      |(cellLoad w s c : ℝ) - μ c| := by
    intro c
    by_cases h : cap c ≤ cellLoad w s c
    · rw [Nat.cast_sub h]
      exact (sub_le_sub_left (hc c) _).trans (le_abs_self _)
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h), Nat.cast_zero]
      exact abs_nonneg _
  have hs : (overflow w cap s : ℝ) ≤ ∑ c : C, |(cellLoad w s c : ℝ) - μ c| := by
    unfold overflow
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun c _ => hpoint c)
  calc
    (overflow w cap s : ℝ)^2 ≤ (∑ c : C, |(cellLoad w s c : ℝ) - μ c|)^2 := by
      gcongr
    _ ≤ (Fintype.card C : ℝ) * ∑ c, ((cellLoad w s c : ℝ) - μ c)^2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : C => (1 : ℝ))
        (fun c => |(cellLoad w s c : ℝ) - μ c|)

/-- A deterministic finite realization of the loss bound after the
squared deviations have been supplied, as in the conditional-expectation step of P9. -/
theorem retain_from_deviations {E C : Type*} [DecidableEq E] [Fintype C]
    (w : E → C → ℕ) (cap : C → ℕ) (s : Finset E)
    (μ : C → ℝ) (hc : ∀ c, μ c ≤ (cap c : ℝ)) (B : ℝ)
    (hB : 0 ≤ B) (hd : (∑ c, ((cellLoad w s c : ℝ) - μ c)^2) ≤ B) :
    ∃ t : Finset E, t ⊆ s ∧ (∀ c, cellLoad w t c ≤ cap c) ∧
      (s.card : ℝ) ≤ (t.card : ℝ) + Real.sqrt ((Fintype.card C : ℝ) * B) := by
  obtain ⟨t, hts, htcap, htcount⟩ := keep_within_capacity w cap s
  have hsq := (overflow_sq_le w cap s μ hc).trans (mul_le_mul_of_nonneg_left hd (by positivity))
  have hrt : (overflow w cap s : ℝ) ≤ Real.sqrt ((Fintype.card C : ℝ) * B) :=
    (Real.le_sqrt (by positivity) (by positivity)).2 hsq
  refine ⟨t, hts, htcap, ?_⟩
  have hcount : (s.card : ℝ) ≤ (t.card : ℝ) + (overflow w cap s : ℝ) := by
    exact_mod_cast htcount
  linarith


/-- Finite seating with the exact P9 loss: the starting count error and the
cell-deviation error add, with each logical port actually placed in its own cell. -/
theorem seat_from_deviations {E I : Type*} [DecidableEq E] [Fintype (I → Bool)]
    [DecidableEq (I → Bool)] (label : E → Bool → I → Bool)
    (s : Finset E) (b : ℕ) (right : Bool) (μ : (I → Bool) → ℝ)
    (hc : ∀ c, μ c ≤ (b : ℝ)) (target slack B : ℝ)
    (hB : 0 ≤ B) (hmarks : target ≤ (s.card : ℝ) + slack)
    (hd : (∑ c : I → Bool, ((cellLoad (multiplicity label) s c : ℝ) - μ c)^2) ≤ B) :
    ∃ t : Finset E, t ⊆ s ∧
      (∀ c : I → Bool, Nonempty (markedPort label t c ↪
        {p : (I → Bool) × Fin b // endMask right p.1 = c})) ∧
      target ≤ (t.card : ℝ) + slack + Real.sqrt ((Fintype.card (I → Bool) : ℝ) * B) := by
  obtain ⟨t, hts, htc, htb⟩ := retain_from_deviations
    (multiplicity label) (fun _ => b) s μ hc B hB hd
  refine ⟨t, hts, fun c => seat_markedPorts label t b right c c (htc c), ?_⟩
  linarith

/-- All retained equalities are in the unsupported-column count for
this sign, when both of their physical column ports were seated at the endpoint. -/
theorem protected_card_le_unsupported {E : Type*} [DecidableEq E]
    (all keep : Finset E) (hkeep : keep ⊆ all)
    (slot : E → Bool → ℕ) {L : ℕ} (hL : 0 < L)
    (right : Bool) {t : ℤ} (ht : if right then t < 0 else 0 < t)
    (hseat : ∀ e ∈ keep, ∀ p, slot e p = endpoint L right) :
    keep.card ≤ (all.filter fun e => ∀ p : Bool, ∀ x : Fin L,
      (x.val : ℤ) + t ≠ (slot e p : ℤ)).card := by
  classical
  apply Finset.card_le_card
  intro e he
  apply Finset.mem_filter.mpr
  refine ⟨hkeep he, ?_⟩
  intro p x
  exact protected_eq_has_no_predecessor slot hL right ht (hseat e he) p x.val x.isLt

#print axioms endMask_at_physical_endpoint
#print axioms seat_from_deviations
#print axioms protected_card_le_unsupported
#print axioms seat_markedPorts
#print axioms overflow_sq_le
#print axioms retain_from_deviations
#print axioms overflow_erase_lt
#print axioms keep_within_capacity
#print axioms endpoint_no_predecessor
#print axioms protected_eq_has_no_predecessor
#print axioms card_endpointSeats

end GuardedPacking
