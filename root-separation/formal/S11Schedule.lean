
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.Interval
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace S11

open scoped BigOperators

/-- Appendix D, contraction lines 76–97. The root size parameter s
    is retained at lower depths. -/
def lambda (s : ℕ) : ℕ := Nat.clog 2 s
def ceilDiv (x y : ℕ) : ℕ := (x + y - 1) / y
def leafThreshold (s : ℕ) : ℕ := ceilDiv s (Nat.sqrt (lambda s))
def retained (s depth : ℕ) : ℕ := lambda s / (131072 * 2 ^ depth)
def labelLength (s depth : ℕ) : ℕ :=
  2 * ∑ j ∈ Finset.range (depth + 1), retained s j
def packetLength (s depth : ℕ) : ℕ := 2 ^ labelLength s depth
def probeCount (M L : ℕ) : ℕ := M * (2 * L - 1) + 1

def level (t : ℤ) : ℕ := padicValNat 2 t.natAbs
def centers (u L : ℕ) : Finset ℤ :=
  (Finset.Ico (-(L : ℤ)) L).filter fun t => t ≠ 0 ∧ level t < u
def taper (M u : ℕ) : ℕ := ceilDiv (3 * M) u
def multiplicity (M u : ℕ) (t : ℤ) : ℕ := taper M u * (u - level t)
def precision (p M a u L : ℕ) (t : ℤ) : ℕ :=
  p + 8 * taper M u * (L / 2 ^ level t) + 8 * M * (a + 1)

theorem root_parameters (s : ℕ) :
    labelLength s 0 = 2 * retained s 0 ∧ packetLength s 0 = 2 ^ (2 * retained s 0) := by
  simp [labelLength, packetLength]

theorem positive_root_threshold (s : ℕ) :
    0 < retained s 0 ↔ 2 ^ (131071 : ℕ) < s := by
  change 1 ≤ lambda s / (131072 * 2^0) ↔ _
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 131072 * 2 ^ 0)]
  change 131071 < Nat.clog 2 s ↔ _
  exact Nat.lt_clog_iff_pow_lt (by decide)

theorem one_active {u L : ℕ} (hu : 0 < u) (hL : 1 < L) : (1 : ℤ) ∈ centers u L := by
  have h : level 1 = 0 := by simp [level]
  simp [centers, h, hu, show (1 : ℤ) < L by exact_mod_cast hL]

theorem three_mul_le_taper_mul {M u : ℕ} (hu : 0 < u) : 3 * M ≤ taper M u * u := by
  have h := Nat.mod_lt (3 * M + u - 1) hu
  have he := Nat.mod_add_div (3 * M + u - 1) u
  unfold taper ceilDiv
  rw [Nat.mul_comm _ u]
  omega

theorem odd_precision_budget (p M a u L : ℕ) (hu : 0 < u) :
    24 * M * L ≤ u * precision p M a u L 1 := by
  have h := Nat.mul_le_mul_left (8 * L) (three_mul_le_taper_mul (M := M) hu)
  have h1 : level 1 = 0 := by simp [level]
  simp only [precision, h1, pow_zero, Nat.div_one]
  calc
    24 * M * L ≤ u * (8 * taper M u * L) := by
      calc
        24 * M * L = (8 * L) * (3 * M) := by ring
        _ ≤ (8 * L) * (taper M u * u) := h
        _ = _ := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

def weightSum : List ℕ → List ℕ → ℕ
  | w :: ws, b :: bs => w * b + weightSum ws bs
  | _, _ => 0

/-- The source's remaining-budget DFS, contraction lines 478–482. -/
def tuples : List ℕ → ℕ → List (List ℕ)
  | [], p => if p = 0 then [] else [[]]
  | w :: ws, p =>
    if p = 0 then []
    else (List.range ((p - 1) / w + 1)).flatMap fun b =>
      (tuples ws (p - w * b)).map (b :: ·)

theorem mem_tuples {ws bs : List ℕ} {p : ℕ} (hweights : ∀ w ∈ ws, 0 < w) :
    bs ∈ tuples ws p ↔ bs.length = ws.length ∧ weightSum ws bs < p := by
  induction ws generalizing bs p with
  | nil =>
    cases bs <;> by_cases hp : p = 0 <;> simp [tuples, hp, weightSum, Nat.pos_of_ne_zero]
  | cons w ws ih =>
    have hw := hweights w (by simp)
    have hws : ∀ a ∈ ws, 0 < a := fun a ha => hweights a (by simp [ha])
    cases bs with
    | nil => by_cases hp : p = 0 <;> simp [tuples, hp, List.mem_flatMap, List.mem_map]
    | cons b bs =>
      by_cases hp : p = 0
      · simp [tuples, hp]
      simp only [tuples, hp, ↓reduceIte, List.mem_flatMap, List.mem_range, List.mem_map,
        List.cons.injEq, exists_eq_right_right, List.length_cons, Nat.add_right_cancel_iff,
        weightSum]
      constructor
      · rintro ⟨_, hmem⟩
        have hb := ((ih hws).1 hmem)
        exact ⟨hb.1, by omega⟩
      · rintro ⟨hlen, hlt⟩
        refine ⟨?_, (ih hws).2 ⟨hlen, by omega⟩⟩
        apply Nat.lt_succ_of_le
        apply (Nat.le_div_iff_mul_le hw).2
        rw [Nat.mul_comm]
        omega

/-- Fold the same DFS without ever building the complete tuple list.
    The accumulator is threaded through a complete branch before trying
    the next exponent. -/
def foldTuples {A : Type*} : List ℕ → ℕ → (A → List ℕ → A) → A → A
  | [], p, step, init => if p = 0 then init else step init []
  | w :: ws, p, step, init =>
    if p = 0 then init else
      (List.range ((p-1)/w+1)).foldl
        (fun st b => foldTuples ws (p-w*b) (fun st' bs => step st' (b :: bs)) st) init

private theorem foldl_flatMap {A B C : Type*} (step : A → C → A) (f : B → List C)
    (xs : List B) (init : A) :
    (xs.flatMap f).foldl step init = xs.foldl (fun st b => (f b).foldl step st) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons b bs ih => simp [List.flatMap_cons, List.foldl_append, ih]

theorem foldTuples_eq {A : Type*} (ws : List ℕ) (p : ℕ)
    (step : A → List ℕ → A) (init : A) :
    foldTuples ws p step init = (tuples ws p).foldl step init := by
  induction ws generalizing p step init with
  | nil => by_cases hp : p = 0 <;> simp [foldTuples, tuples, hp]
  | cons w ws ih =>
    by_cases hp : p = 0 <;> simp [foldTuples, tuples, hp, foldl_flatMap, List.foldl_map, ih]

section Loop
variable {R : Type*} [CommSemiring R]

/-- The tile index is a residue mod 2^(i+1) and b+1 is the mode weight. -/
abbrev Mode (B : Type*) (i p : ℕ) := B × Fin (2 ^ (i + 1)) × Fin (p - 1)

noncomputable def modes (B : Type*) [Fintype B] (i p : ℕ) : List (Mode B i p) := by
  classical
  exact Finset.univ.toList

noncomputable def modeWeights (B : Type*) [Fintype B] (i p : ℕ) : List ℕ :=
  (modes B i p).map fun m => m.2.2.val + 1

/-- The address of one complete inner product accumulation. -/
structure Slot where
  center : ℤ
  probe : ℕ
  exponents : List ℕ
deriving DecidableEq

noncomputable def batch (B : Type*) [Fintype B] (t : ℤ) (j p : ℕ) : List Slot :=
  (tuples (modeWeights B (level t) p) p).map (Slot.mk t j)

/-- The source loops over every active center and every probe.
    B t is the type of unequal-symbol packets at t. -/
noncomputable def rootSlots (u M L a p : ℕ) (B : ℤ → Type*) [∀ t, Fintype (B t)] :
    List Slot :=
  (centers u L).toList.flatMap fun t =>
    (List.range (probeCount M L)).flatMap fun j =>
      batch (B t) t j (precision p M a u L t)

/-- An inner iteration consumes one child result per group and adds
    their product to the current sample. -/
def runBatch {G : Type*} (groups : List G) (child : Slot → G → R)
    (slots : List Slot) : R × List Slot :=
  slots.foldl (fun st b => (st.1 + (groups.map (child b)).prod, b :: st.2)) (0, [])

private theorem trace_fold {G : Type*} (groups : List G) (child : Slot → G → R)
    (slots : List Slot) (st : R × List Slot) :
    (slots.foldl (fun x b => (x.1 + (groups.map (child b)).prod, b :: x.2)) st).2 =
      slots.reverse ++ st.2 := by
  induction slots generalizing st with
  | nil => simp
  | cons b bs ih => simp [List.foldl_cons, ih, List.reverse_cons, List.append_assoc]

theorem runBatch_trace {G : Type*} (groups : List G)
    (child : Slot → G → R) (slots : List Slot) :
    (runBatch groups child slots).2 = slots.reverse := by
  simp [runBatch, trace_fold]

private theorem sum_fold {G : Type*} (groups : List G) (child : Slot → G → R)
    (slots : List Slot) (st : R × List Slot) :
    (slots.foldl (fun x b => (x.1 + (groups.map (child b)).prod, b :: x.2)) st).1 =
      st.1 + (slots.map (fun b => (groups.map (child b)).prod)).sum := by
  induction slots generalizing st with
  | nil => simp
  | cons b bs ih => simp [List.foldl_cons, ih, add_assoc]

theorem runBatch_value {G : Type*} (groups : List G)
    (child : Slot → G → R) (slots : List Slot) :
    (runBatch groups child slots).1 =
      (slots.map (fun b => (groups.map (child b)).prod)).sum := by
  simp [runBatch, sum_fold]

private theorem list_flatMap_length_bound {α β : Type*} (l : List α) (f : α → List β) {x : α} (hx : x ∈ l) :
    (f x).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 hx with h | h
    · subst y
      omega
    · have := ih h
      omega

theorem batch_le_root (u M L a p : ℕ) (B : ℤ → Type*) [∀ t, Fintype (B t)]
    {t : ℤ} (ht : t ∈ centers u L) {j : ℕ} (hj : j < probeCount M L) :
    (batch (B t) t j (precision p M a u L t)).length ≤ (rootSlots u M L a p B).length := by
  unfold rootSlots
  refine (list_flatMap_length_bound (List.range (probeCount M L))
    (fun j => batch (B t) t j (precision p M a u L t)) (List.mem_range.2 hj)).trans ?_
  exact list_flatMap_length_bound (centers u L).toList
    (fun t => (List.range (probeCount M L)).flatMap fun j =>
      batch (B t) t j (precision p M a u L t)) (Finset.mem_toList.2 ht)

end Loop

#print axioms root_parameters
#print axioms positive_root_threshold
#print axioms one_active
#print axioms odd_precision_budget
#print axioms mem_tuples
#print axioms foldTuples_eq
#print axioms runBatch_trace
#print axioms runBatch_value
#print axioms batch_le_root

end S11

