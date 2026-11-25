import ExpansionGraphCNF
import Mathlib.Data.List.Nodup

/-!
# Supplied-edge construction for Appendix A.2

The construction takes a list of pairs of padded vertices, with one pair per
edge. It labels each fresh variable by the edge's position, using an increasing
cursor. Graph validation, endpoint sorting, and edge lookup are unnecessary
during construction. A proof of validity is used only to compare the result
with the abstract graph model.

The cost is for a word-record model with constant-time list inspection,
field access, label tagging, record construction, and word arithmetic. A
list inspection includes returning its head and tail. Fixed Booleans and
the empty list need no allocation. Index bounds are proofs. In particular,
a length appearing only in a bound or type is not a runtime scan.
The step counter records the modeled operations. Computing or storing the
counter itself is instrumentation.
-/

namespace Reconstruction.ExpansionGraph

/-- Output and operation count of the instrumented construction. -/
structure Metered (A : Type*) where
  output : A
  steps : ℕ

abbrev EdgeInput (n : ℕ) := List (PaddedVar n × PaddedVar n)
abbrev OutputVar (n m : ℕ) := PaddedVar n ⊕ Fin m

private def literalCount {X : Type*} : CNF X → ℕ
  | [] => 0
  | C :: F => C.length + literalCount F

-- Each cons branch inspects the list, reads the literal's two fields, writes
-- two label tags, builds one literal pair and links one literal list cell.
private def copyOriginalClause {n m : ℕ} : List (Fin n × Bool) →
    Metered (List (OutputVar n m × Bool))
  | [] => ⟨[], 1⟩
  | l :: C =>
    let c := copyOriginalClause (m := m) C
    let v : OutputVar n m := .inl (.inl l.1)
    ⟨(v,l.2) :: c.output, c.steps + 7⟩

-- Add two operations per clause: one inspection and one clause list cell.
private def copyOriginal {n m : ℕ} (tail : CNF (OutputVar n m)) :
    CNF (Fin n) → Metered (CNF (OutputVar n m))
  | [] => ⟨tail, 1⟩
  | C :: F =>
    let c := copyOriginalClause (m := m) C
    let r := copyOriginal tail F
    ⟨c.output :: r.output, c.steps + r.steps + 2⟩

-- A positive counter branch tests and decrements the counter, writes two
-- label tags, constructs a literal pair, and links one cell in each list.
private def emitPadding {n m : ℕ} (tail : CNF (OutputVar n m)) :
    (k : ℕ) → k ≤ paddingCount n → Metered (CNF (OutputVar n m))
  | 0, _ => ⟨tail, 1⟩
  | k + 1, h =>
    let v : OutputVar n m := .inl (.inr ⟨k, by omega⟩)
    let r := emitPadding tail k (by omega)
    ⟨[(v,false)] :: r.output, r.steps + 7⟩

private def prependGate {n m : ℕ} (z : Fin m) (u v : PaddedVar n)
    (tail : CNF (OutputVar n m)) : CNF (OutputVar n m) :=
  let x : OutputVar n m := .inl u
  let y : OutputVar n m := .inl v
  let g : OutputVar n m := .inr z
  [(g,false), (x,true)] :: [(g,false), (y,true)] ::
    [(g,true), (x,false), (y,false)] :: tail

-- One list inspection, two endpoint reads, one cursor increment, three
-- label tags, seven literal pairs, seven literal cells, and three clause
-- cells. The final empty-list inspection costs one.
private def emitEdges {n m : ℕ} :
    (L : EdgeInput n) → (i : ℕ) → i + L.length ≤ m → Metered (CNF (OutputVar n m))
  | [], _, _ => ⟨[], 1⟩
  | (u,v) :: L, i, h =>
    let z : Fin m := ⟨i, by simp only [List.length_cons] at h; omega⟩
    let r := emitEdges L (i+1) (by simp only [List.length_cons] at h; omega)
    ⟨prependGate z u v r.output, r.steps + 24⟩

/-- Build the padded gate extension from the formula and a supplied list of
edges. Padding arithmetic uses two remainders and one subtraction. The
construction uses the already built suffix at each stage. -/
def constructFromEdges {n : ℕ} (F : CNF (Fin n)) (L : EdgeInput n) :
    Metered (CNF (OutputVar n L.length)) :=
  let gates := emitEdges L 0 (by simp)
  let padded := emitPadding gates.output (paddingCount n) le_rfl
  let result := copyOriginal padded.output F
  ⟨result.output, 3 + gates.steps + padded.steps + result.steps⟩

private theorem copyOriginalClause_length {n m : ℕ} (C : List (Fin n × Bool)) :
    (copyOriginalClause (m := m) C).output.length = C.length := by
  induction C with
  | nil => rfl
  | cons l C ih => simp only [copyOriginalClause, List.length_cons, ih]

private theorem copyOriginal_shape {n m : ℕ} (tail : CNF (OutputVar n m)) (F : CNF (Fin n)) :
    (copyOriginal tail F).output.length = F.length + tail.length ∧
      literalCount (copyOriginal tail F).output = literalCount F + literalCount tail := by
  induction F with
  | nil => simp [copyOriginal, literalCount]
  | cons C F ih =>
    simp only [copyOriginal, List.length_cons, literalCount, copyOriginalClause_length, ih.1, ih.2]
    omega

private theorem emitPadding_shape {n m : ℕ} (tail : CNF (OutputVar n m))
    (k : ℕ) (h : k ≤ paddingCount n) :
    (emitPadding tail k h).output.length = k + tail.length ∧
      literalCount (emitPadding tail k h).output = k + literalCount tail := by
  induction k with
  | zero => simp [emitPadding]
  | succ k ih =>
    simp only [emitPadding, List.length_cons, List.length_nil, literalCount, (ih _).1, (ih _).2]
    omega

private theorem emitEdges_shape {n m : ℕ} (L : EdgeInput n) (i : ℕ) (h : i + L.length ≤ m) :
    (emitEdges L i h).output.length = 3*L.length ∧
      literalCount (emitEdges L i h).output = 7*L.length := by
  induction L generalizing i with
  | nil => simp [emitEdges, literalCount]
  | cons uv L ih =>
    obtain ⟨u,v⟩ := uv
    simp only [emitEdges, prependGate, List.length_cons, List.length_nil, literalCount,
      (ih _ _).1, (ih _ _).2]
    omega

private theorem literalCount_eq_sum {X : Type*} (F : CNF X) :
    literalCount F = (F.map List.length).sum := by
  induction F with
  | nil => rfl
  | cons C F ih => simp [literalCount, ih]

/-- Exact emitted clause and literal counts. Empty input clauses still
occupy a clause record and remain in the output. -/
theorem constructFromEdges_shape {n : ℕ} (F : CNF (Fin n)) (L : EdgeInput n) :
    (constructFromEdges F L).output.length = F.length + paddingCount n + 3*L.length ∧
      (((constructFromEdges F L).output.map List.length).sum) =
        (F.map List.length).sum + paddingCount n + 7*L.length := by
  rw [← literalCount_eq_sum (constructFromEdges F L).output, ← literalCount_eq_sum F]
  simp only [constructFromEdges, (copyOriginal_shape _ _).1, (copyOriginal_shape _ _).2,
    (emitPadding_shape _ _ _).1, (emitPadding_shape _ _ _).2,
    (emitEdges_shape _ _ _).1, (emitEdges_shape _ _ _).2]
  omega

private theorem copyOriginalClause_steps {n m : ℕ} (C : List (Fin n × Bool)) :
    (copyOriginalClause (m := m) C).steps = 1 + 7*C.length := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [copyOriginalClause, List.length_cons, ih]
    omega

private theorem copyOriginal_steps {n m : ℕ} (tail : CNF (OutputVar n m)) (F : CNF (Fin n)) :
    (copyOriginal tail F).steps = 1 + 3*F.length + 7*literalCount F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simp only [copyOriginal, List.length_cons, literalCount, copyOriginalClause_steps, ih]
    omega

private theorem emitPadding_steps {n m : ℕ} (tail : CNF (OutputVar n m))
    (k : ℕ) (h : k ≤ paddingCount n) :
    (emitPadding tail k h).steps = 1 + 7*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [emitPadding, ih]
    omega

private theorem emitEdges_steps {n m : ℕ} (L : EdgeInput n) (i : ℕ) (h : i + L.length ≤ m) :
    (emitEdges L i h).steps = 1 + 24*L.length := by
  induction L generalizing i with
  | nil => rfl
  | cons uv L ih =>
    obtain ⟨u,v⟩ := uv
    simp only [emitEdges, List.length_cons, ih]
    omega

/-- The full construction cost, including formula copying and padding. -/
theorem constructFromEdges_steps {n : ℕ} (F : CNF (Fin n)) (L : EdgeInput n) :
    (constructFromEdges F L).steps =
      6 + 3*F.length + 7*((F.map List.length).sum) + 7*paddingCount n + 24*L.length := by
  simp only [constructFromEdges, emitEdges_steps, emitPadding_steps, copyOriginal_steps,
    literalCount_eq_sum]
  omega

/-- The at-most-127 padding units add a constant to the linear bound. -/
theorem constructFromEdges_linear {n : ℕ} (F : CNF (Fin n)) (L : EdgeInput n) :
    (constructFromEdges F L).steps ≤
      895 + 24*(F.length + (F.map List.length).sum + L.length) := by
  rw [constructFromEdges_steps]
  have hp := paddingCount_le n
  omega

private theorem sat_cons {X : Type*} (C : List (X × Bool)) (F : CNF X) (x : X → Bool) :
    Satisfies (C :: F) x ↔ (∃ l ∈ C, x l.1 = l.2) ∧ Satisfies F x := by
  constructor
  · intro h
    exact ⟨h _ (List.mem_cons_self ..), fun D hD => h D (List.mem_cons_of_mem _ hD)⟩
  · intro h D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact h.1
    · exact h.2 D hD

private theorem literal_cons {X : Type*} (a : X × Bool) (C : List (X × Bool)) (x : X → Bool) :
    (∃ l ∈ a :: C, x l.1 = l.2) ↔ x a.1 = a.2 ∨ ∃ l ∈ C, x l.1 = l.2 := by
  constructor
  · rintro ⟨l, hl, he⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Or.inl he
    · exact Or.inr ⟨l,hl,he⟩
  · rintro (he | ⟨l,hl,he⟩)
    · exact ⟨a,List.mem_cons_self ..,he⟩
    · exact ⟨l,List.mem_cons_of_mem _ hl,he⟩

private theorem copyOriginalClause_sat {n m : ℕ} (C : List (Fin n × Bool))
    (x : OutputVar n m → Bool) :
    (∃ l ∈ (copyOriginalClause C).output, x l.1 = l.2) ↔
      (∃ l ∈ C, x (.inl (.inl l.1)) = l.2) := by
  induction C with
  | nil => simp [copyOriginalClause]
  | cons l C ih =>
    rw [copyOriginalClause, literal_cons, ih]
    constructor
    · rintro (h | ⟨p,hp,hx⟩)
      · exact ⟨l,List.mem_cons_self ..,h⟩
      · exact ⟨p,List.mem_cons_of_mem _ hp,hx⟩
    · rintro ⟨p,hp,hx⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inl hx
      · exact Or.inr ⟨p,hp,hx⟩

private theorem copyOriginal_sat {n m : ℕ} (tail : CNF (OutputVar n m))
    (F : CNF (Fin n)) (x : OutputVar n m → Bool) :
    Satisfies (copyOriginal tail F).output x ↔
      Satisfies F (fun v => x (.inl (.inl v))) ∧ Satisfies tail x := by
  induction F with
  | nil => simp [copyOriginal, Satisfies]
  | cons C F ih =>
    rw [copyOriginal, sat_cons, sat_cons C, copyOriginalClause_sat, ih]
    exact and_assoc.symm

private theorem emitPadding_sat {n m : ℕ} (tail : CNF (OutputVar n m))
    (k : ℕ) (h : k ≤ paddingCount n) (x : OutputVar n m → Bool) :
    Satisfies (emitPadding tail k h).output x ↔
      (∀ v : Fin (paddingCount n), v.val < k → x (.inl (.inr v)) = false) ∧ Satisfies tail x := by
  induction k with
  | zero => simp [emitPadding]
  | succ k ih =>
    rw [emitPadding, sat_cons, literal_cons, ih]
    simp only [List.not_mem_nil, false_and, exists_false, or_false]
    constructor
    · rintro ⟨hLast,hPrior,hTail⟩
      refine ⟨fun v hv => ?_, hTail⟩
      by_cases hV : v.val < k
      · exact hPrior v hV
      · have hv' : v = ⟨k, by omega⟩ := Fin.ext (show v.val = k by omega)
        simpa only [hv'] using hLast
    · rintro ⟨hAll,hTail⟩
      exact ⟨hAll ⟨k, by omega⟩ (by simp), fun v hv => hAll v (by omega), hTail⟩

private theorem prependGate_sat {n m : ℕ} (z : Fin m) (u v : PaddedVar n)
    (tail : CNF (OutputVar n m)) (x : OutputVar n m → Bool) :
    Satisfies (prependGate z u v tail) x ↔
      x (.inr z) = (x (.inl u) && x (.inl v)) ∧ Satisfies tail x := by
  simp only [prependGate, sat_cons, literal_cons, List.not_mem_nil, false_and, exists_false, or_false]
  cases x (.inr z) <;> cases x (.inl u) <;> cases x (.inl v) <;> simp

private def edgeSlot {n m : ℕ} (L : EdgeInput n) (i : ℕ) (h : i + L.length ≤ m)
    (j : Fin L.length) : Fin m := ⟨i + j.val, by have := j.isLt; omega⟩

private theorem emitEdges_sat {n m : ℕ} (L : EdgeInput n) (i : ℕ)
    (h : i + L.length ≤ m) (x : OutputVar n m → Bool) :
    Satisfies (emitEdges L i h).output x ↔
      ∀ j : Fin L.length, x (.inr (edgeSlot L i h j)) =
        (x (.inl (L.get j).1) && x (.inl (L.get j).2)) := by
  induction L generalizing i with
  | nil =>
    constructor
    · intro _ j
      exact Fin.elim0 j
    · intro _
      simp [emitEdges, Satisfies]
  | cons uv L ih =>
    obtain ⟨u,v⟩ := uv
    rw [emitEdges, prependGate_sat, ih]
    constructor
    · rintro ⟨hFirst,hRest⟩ j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa [edgeSlot] using hFirst
      · simpa [edgeSlot, List.get_cons_succ', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hRest k
    · intro hAll
      refine ⟨?_, fun j => ?_⟩
      · simpa [edgeSlot] using hAll ⟨0, by simp⟩
      · simpa [edgeSlot, List.get_cons_succ', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hAll j.succ

/-- Semantics of the executable output, in the identifiers used by the
algorithm. The gate equation is imposed for every supplied edge record. -/
theorem constructFromEdges_sat {n : ℕ} (F : CNF (Fin n)) (L : EdgeInput n)
    (x : OutputVar n L.length → Bool) :
    Satisfies (constructFromEdges F L).output x ↔
      Satisfies F (fun v => x (.inl (.inl v))) ∧
      (∀ v : Fin (paddingCount n), x (.inl (.inr v)) = false) ∧
      ∀ j : Fin L.length, x (.inr j) = (x (.inl (L.get j).1) && x (.inl (L.get j).2)) := by
  simp only [constructFromEdges, copyOriginal_sat, emitPadding_sat, Fin.isLt, true_implies,
    emitEdges_sat]
  have h (j : Fin L.length) : edgeSlot L 0 (by simp) j = j := Fin.ext (Nat.zero_add _)
  simp only [h]

end Reconstruction.ExpansionGraph
