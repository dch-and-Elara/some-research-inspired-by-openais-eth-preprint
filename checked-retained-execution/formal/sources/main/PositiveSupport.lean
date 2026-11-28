import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Boolean-cube semantics of positive arithmetic DAGs for Section F3.
A register can be named any number of times, including twice by one product.
Gate inputs are finite multilinear coefficient tables over an ordered field.
The nonnegative-coefficient condition is imposed only on input tables. -/

namespace PositiveSupport

open scoped BigOperators

variable {V K : Type*} [Fintype V] [DecidableEq V]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Coefficients in the basis of squarefree Boolean monomials. -/
structure Form (V K : Type*) [Zero K] [LE K] where
  coeff : Finset V → K
  nonneg : ∀ A, 0 ≤ coeff A

namespace Form

/-- Evaluation at the characteristic vector of the enabled vertices. -/
def value (p : Form V K) (X : Finset V) : K := ∑ A ∈ X.powerset, p.coeff A

def add (p q : Form V K) : Form V K :=
  ⟨fun A => p.coeff A + q.coeff A, fun A => add_nonneg (p.nonneg A) (q.nonneg A)⟩

/-- Multiplying on the Boolean cube identifies repetitions by set union. -/
def product (p q : Form V K) : Form V K where
  coeff U := ∑ A : Finset V, ∑ B : Finset V, if A ∪ B = U then p.coeff A * q.coeff B else 0
  nonneg U := Finset.sum_nonneg fun A _ => Finset.sum_nonneg fun B _ =>
    by split <;> first | exact mul_nonneg (p.nonneg A) (q.nonneg B) | exact le_rfl

omit [Fintype V] [DecidableEq V] in
theorem value_add (p q : Form V K) (X : Finset V) :
    (p.add q).value X = p.value X + q.value X := by
  simp [value, add, Finset.sum_add_distrib]

omit [IsStrictOrderedRing K] in
private theorem value_sum (p : Form V K) (X : Finset V) :
    p.value X = ∑ A : Finset V, if A ⊆ X then p.coeff A else 0 := by
  unfold value
  rw [← Finset.sum_filter]
  have hs : (Finset.univ.filter fun A : Finset V => A ⊆ X) = X.powerset := by
    ext A
    simp
  rw [hs]

theorem value_product (p q : Form V K) (X : Finset V) :
    (p.product q).value X = p.value X * q.value X := by
  classical
  calc
    (p.product q).value X =
        ∑ A : Finset V, ∑ B : Finset V, ∑ U ∈ X.powerset,
          if A ∪ B = U then p.coeff A * q.coeff B else 0 := by
      unfold value product
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.sum_comm]
    _ = ∑ A : Finset V, ∑ B : Finset V,
        (if A ⊆ X then p.coeff A else 0) * (if B ⊆ X then q.coeff B else 0) := by
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      by_cases ha : A ⊆ X <;> by_cases hb : B ⊆ X <;>
        simp [Finset.sum_ite_eq, Finset.union_subset_iff, ha, hb]
    _ = p.value X * q.value X := by
      rw [value_sum, value_sum q, Finset.sum_mul_sum]

omit [Fintype V] [DecidableEq V] in
theorem add_pos (p q : Form V K) (U : Finset V) :
    0 < (p.add q).coeff U ↔ 0 < p.coeff U ∨ 0 < q.coeff U := by
  change 0 < p.coeff U + q.coeff U ↔ _
  have hp := p.nonneg U
  have hq := q.nonneg U
  constructor
  · intro h
    by_cases h' : 0 < p.coeff U
    · exact Or.inl h'
    · exact Or.inr (by linarith)
  · rintro (h | h) <;> linarith

theorem product_pos (p q : Form V K) (U : Finset V) :
    0 < (p.product q).coeff U ↔
      ∃ A B, 0 < p.coeff A ∧ 0 < q.coeff B ∧ A ∪ B = U := by
  let w (A B : Finset V) := if A ∪ B = U then p.coeff A * q.coeff B else 0
  have hw (A B : Finset V) : 0 ≤ w A B := by
    dsimp [w]
    split <;> first | exact mul_nonneg (p.nonneg A) (q.nonneg B) | exact le_rfl
  change (0 < ∑ A : Finset V, ∑ B : Finset V, w A B) ↔ _
  rw [Finset.sum_pos_iff_of_nonneg fun A _ => Finset.sum_nonneg (fun B _ => hw A B)]
  constructor
  · rintro ⟨A, _, ha⟩
    obtain ⟨B, _, hb⟩ := (Finset.sum_pos_iff_of_nonneg (fun B _ => hw A B)).1 ha
    by_cases h : A ∪ B = U
    · have hab : 0 < p.coeff A * q.coeff B := by simpa [w, h] using hb
      exact ⟨A, B, pos_of_mul_pos_left hab (q.nonneg B),
        pos_of_mul_pos_right hab (p.nonneg A), h⟩
    · simp [w, h] at hb
  · rintro ⟨A, B, hA, hB, h⟩
    exact ⟨A, Finset.mem_univ _, (Finset.sum_pos_iff_of_nonneg (fun B _ => hw A B)).2
      ⟨B, Finset.mem_univ _, by simpa [w, h] using mul_pos hA hB⟩⟩

omit [Fintype V] [IsStrictOrderedRing K] in
/-- Agreement on Boolean inputs determines every multilinear coefficient. -/
theorem coeff_eq_of_values {p q : Form V K} (h : ∀ X, p.value X = q.value X)
    (A : Finset V) : p.coeff A = q.coeff A := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    have e := h A
    change (∑ B ∈ A.powerset, p.coeff B) = ∑ B ∈ A.powerset, q.coeff B at e
    rw [← Finset.sum_erase_add _ _ (Finset.mem_powerset_self A),
      ← Finset.sum_erase_add _ _ (Finset.mem_powerset_self A)] at e
    have es : (∑ B ∈ A.powerset.erase A, p.coeff B) = ∑ B ∈ A.powerset.erase A, q.coeff B := by
      exact Finset.sum_congr rfl fun B hB => ih B (Finset.mem_ssubsets.mp hB)
    rw [es] at e
    exact add_left_cancel e

end Form

/-- Register i can read any of the registers 0 through i-1. -/
inductive Gate (V K : Type*) [Zero K] [LE K] (i : ℕ) where
  | atom (p : Form V K)
  | add (a b : Fin i)
  | mul (a b : Fin i)

abbrev Program (V K : Type*) [Zero K] [LE K] := (i : ℕ) → Gate V K i

/-- Only the finite prefix ending at the selected output register is used. -/
def forms (P : Program V K) (i : ℕ) : Form V K :=
  match P i with
  | .atom p => p
  | .add a b => (forms P a.val).add (forms P b.val)
  | .mul a b => (forms P a.val).product (forms P b.val)
termination_by i
decreasing_by all_goals first | exact a.isLt | exact b.isLt

def scalar (P : Program V K) (X : Finset V) (i : ℕ) : K :=
  match P i with
  | .atom p => p.value X
  | .add a b => scalar P X a.val + scalar P X b.val
  | .mul a b => scalar P X a.val * scalar P X b.val
termination_by i
decreasing_by all_goals first | exact a.isLt | exact b.isLt

theorem scalar_semantics (P : Program V K) (X : Finset V) (i : ℕ) :
    (forms P i).value X = scalar P X i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [forms, scalar]
    cases P i with
    | atom => rfl
    | add a b => exact (Form.value_add _ _ _).trans (congrArg₂ (· + ·) (ih a a.isLt) (ih b b.isLt))
    | mul a b => exact (Form.value_product _ _ _).trans (congrArg₂ (· * ·) (ih a a.isLt) (ih b b.isLt))

def Term (P : Program V K) (i : ℕ) (A : Finset V) := 0 < (forms P i).coeff A

theorem term_atom {P : Program V K} {i : ℕ} {p : Form V K} (h : P i = .atom p) (A : Finset V) :
    Term P i A ↔ 0 < p.coeff A := by rw [Term, forms, h]

theorem term_add {P : Program V K} {i : ℕ} {a b : Fin i} (h : P i = .add a b) (A : Finset V) :
    Term P i A ↔ Term P a A ∨ Term P b A := by
  unfold Term
  rw [forms, h]
  apply Form.add_pos

theorem term_mul {P : Program V K} {i : ℕ} {a b : Fin i} (h : P i = .mul a b) (U : Finset V) :
    Term P i U ↔ ∃ A B, Term P a A ∧ Term P b B ∧ A ∪ B = U := by
  unfold Term
  rw [forms, h]
  apply Form.product_pos

/-- A one-hole occurrence in an unrolled derivation, addressed by the original
register number. At a product the sibling register supplies an arbitrary term,
even if that register is itself the hole register. -/
inductive Context (P : Program V K) (hole : ℕ) : ℕ → Finset V → Prop where
  | here : Context P hole hole ∅
  | addLeft {i} {a b : Fin i} {C} (op : P i = .add a b) :
      Context P hole a C → Context P hole i C
  | addRight {i} {a b : Fin i} {C} (op : P i = .add a b) :
      Context P hole b C → Context P hole i C
  | mulLeft {i} {a b : Fin i} {C B} (op : P i = .mul a b) :
      Context P hole a C → Term P b B → Context P hole i (C ∪ B)
  | mulRight {i} {a b : Fin i} {C B} (op : P i = .mul a b) :
      Term P a B → Context P hole b C → Context P hole i (B ∪ C)

theorem Context.fill {P : Program V K} {g i : ℕ} {A C : Finset V}
    (ctx : Context P g i C) (hA : Term P g A) : Term P i (A ∪ C) := by
  induction ctx with
  | here => simpa using hA
  | addLeft op _ ih => exact (term_add op _).2 (Or.inl ih)
  | addRight op _ ih => exact (term_add op _).2 (Or.inr ih)
  | mulLeft op _ hb ih =>
    exact (term_mul op _).2 ⟨_, _, ih, hb, Finset.union_assoc ..⟩
  | mulRight op hb _ ih =>
    exact (term_mul op _).2 ⟨_, _, hb, ih, by rw [Finset.union_left_comm]⟩

theorem Context.hole_le {P : Program V K} {g i : ℕ} {C : Finset V}
    (ctx : Context P g i C) : g ≤ i := by
  induction ctx with
  | here => exact le_rfl
  | @addLeft i a _ _ _ _ ih => exact ih.trans a.isLt.le
  | @addRight i _ b _ _ _ ih => exact ih.trans b.isLt.le
  | @mulLeft i a _ _ _ _ _ _ ih => exact ih.trans a.isLt.le
  | @mulRight i _ b _ _ _ _ _ ih => exact ih.trans b.isLt.le

/-- Only coefficients of individual atom monomials are bounded. -/
def SmallAtoms (P : Program V K) (last k : ℕ) : Prop :=
  ∀ i ≤ last, ∀ p, P i = .atom p → ∀ A, 0 < p.coeff A → A.card < k

/-- Every large output monomial passes through a product of intermediate
size, and its remaining factors constitute a valid one-hole context. -/
theorem balanced_occurrence {P : Program V K} {last k : ℕ} (hs : SmallAtoms P last k)
    {i : ℕ} (hi : i ≤ last) {U : Finset V} (hu : Term P i U) (hk : k ≤ U.card) :
    ∃ g A C, (∃ a b, P g = .mul a b) ∧ Term P g A ∧ k ≤ A.card ∧ A.card < 2 * k ∧
      Context P g i C ∧ A ∪ C = U := by
  induction i using Nat.strong_induction_on generalizing U with
  | h i ih =>
    cases hop : P i with
    | atom p =>
      exact False.elim (hk.not_gt (hs i hi p hop U ((term_atom hop U).1 hu)))
    | add a b =>
      rcases (term_add hop U).1 hu with ha | hb
      · obtain ⟨g, A, C, hg, hA, hlo, hhi, hc, he⟩ := ih a a.isLt (a.isLt.le.trans hi) ha hk
        exact ⟨g, A, C, hg, hA, hlo, hhi, hc.addLeft hop, he⟩
      · obtain ⟨g, A, C, hg, hA, hlo, hhi, hc, he⟩ := ih b b.isLt (b.isLt.le.trans hi) hb hk
        exact ⟨g, A, C, hg, hA, hlo, hhi, hc.addRight hop, he⟩
    | mul a b =>
      obtain ⟨B, D, hB, hD, rfl⟩ := (term_mul hop U).1 hu
      by_cases hb : k ≤ B.card
      · obtain ⟨g, A, C, hg, hA, hlo, hhi, hc, he⟩ := ih a a.isLt (a.isLt.le.trans hi) hB hb
        exact ⟨g, A, C ∪ D, hg, hA, hlo, hhi, hc.mulLeft hop hD,
          by rw [← Finset.union_assoc, he]⟩
      by_cases hd : k ≤ D.card
      · obtain ⟨g, A, C, hg, hA, hlo, hhi, hc, he⟩ := ih b b.isLt (b.isLt.le.trans hi) hD hd
        exact ⟨g, A, B ∪ C, hg, hA, hlo, hhi, Context.mulRight hop hB hc,
          by rw [Finset.union_left_comm, he]⟩
      · have hcard := Finset.card_union_le B D
        exact ⟨i, B ∪ D, ∅, ⟨a, b, hop⟩, hu, hk, by omega, .here, Finset.union_empty _⟩

/-- A finite simple graph recorded by its actual neighbor lists. -/
structure Graph (V : Type*) where
  nbr : V → Finset V
  symm : ∀ {u v}, u ∈ nbr v → v ∈ nbr u
  loopless : ∀ v, v ∉ nbr v

def Independent (G : Graph V) (A : Finset V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, u ∉ G.nbr v

omit [Fintype V] [DecidableEq V] in
theorem Independent.mono {G : Graph V} {A B : Finset V} (h : Independent G B)
    (sub : A ⊆ B) : Independent G A :=
  fun u hu v hv => h u (sub hu) v (sub hv)

noncomputable def gateVertices (P : Program V K) (g : ℕ) : Finset V := by
  classical exact Finset.univ.filter fun v => ∃ A, Term P g A ∧ v ∈ A

noncomputable def contextVertices (P : Program V K) (g root : ℕ) : Finset V := by
  classical exact Finset.univ.filter fun v => ∃ C, Context P g root C ∧ v ∈ C

theorem gate_mem {P : Program V K} {g : ℕ} {u : V} :
    u ∈ gateVertices P g ↔ ∃ A, Term P g A ∧ u ∈ A := by
  classical simp [gateVertices]

theorem context_mem {P : Program V K} {g r : ℕ} {v : V} :
    v ∈ contextVertices P g r ↔ ∃ C, Context P g r C ∧ v ∈ C := by
  classical simp [contextVertices]

def NoCross (G : Graph V) (S T : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ T, u ∉ G.nbr v

theorem gate_context_no_cross {P : Program V K} {G : Graph V} {r : ℕ}
    (hsound : ∀ U, Term P r U → Independent G U) (g : ℕ) :
    NoCross G (gateVertices P g) (contextVertices P g r) := by
  intro u hu v hv
  obtain ⟨A, ha, hu⟩ := gate_mem.mp hu
  obtain ⟨C, hc, hv⟩ := context_mem.mp hv
  exact hsound _ (hc.fill ha) u (Finset.mem_union_left _ hu) v (Finset.mem_union_right _ hv)

/-- Original graph cut size, counting each crossing edge at its outside endpoint. -/
def cutSize (G : Graph V) (S : Finset V) : ℕ := ∑ v ∈ Sᶜ, (G.nbr v ∩ S).card

/-- All neighbors of a context vertex lie outside the gate support.
Minimum degree bounds the number of context vertices by outside incidences. -/
theorem context_card_le {G : Graph V} {S T : Finset V} (hc : NoCross G S T)
    (hmin : ∀ v, (G.nbr v).Nonempty) {D : ℕ} (hdeg : ∀ v, (G.nbr v).card ≤ D) :
    T.card ≤ Sᶜ.card * D := by
  have cover : T ⊆ Sᶜ.biUnion G.nbr := by
    intro v hv
    obtain ⟨w, hw⟩ := hmin v
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_compl.mpr (fun hs => hc w hs v hv hw), G.symm hw⟩
  exact (Finset.card_le_card cover).trans
    (Finset.card_biUnion_le_card_mul _ _ D (fun v _ => hdeg v))

/-- Only vertices outside both sets can receive an edge of the cut. -/
theorem cut_le_missed {G : Graph V} {S T : Finset V} (hc : NoCross G S T)
    {D : ℕ} (hdeg : ∀ v, (G.nbr v).card ≤ D) :
    cutSize G S ≤ (S ∪ T)ᶜ.card * D := by
  classical
  have hsub : (S ∪ T)ᶜ ⊆ Sᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr fun hs => (Finset.mem_compl.mp hv) (Finset.mem_union_left T hs)
  have he : (∑ v ∈ (S ∪ T)ᶜ, (G.nbr v ∩ S).card) = cutSize G S := by
    apply Finset.sum_subset hsub
    intro v hs hst
    have ht : v ∈ T := by simpa [Finset.mem_compl.mp hs] using hst
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hc w (Finset.mem_inter.mp hw).2 v ht (Finset.mem_inter.mp hw).1
  rw [← he]
  calc
    _ ≤ ∑ _v ∈ (S ∪ T)ᶜ, D := Finset.sum_le_sum fun v _ =>
      (Finset.card_le_card Finset.inter_subset_left).trans (hdeg v)
    _ = _ := by simp

/-- Expansion in the original graph controls missed free vertices even if
S and T overlap. The complement of W accounts for the fixed switches. -/
theorem missed_vertices {G : Graph V} {S T W : Finset V} {k D : ℕ} {h : K}
    (hc : NoCross G S T) (hmin : ∀ v, (G.nbr v).Nonempty)
    (hD : 0 < D) (hdeg : ∀ v, (G.nbr v).card ≤ D) (hh : 0 ≤ h)
    (expand : ∀ U, h * (min U.card Uᶜ.card : ℕ) ≤ (cutSize G U : K))
    (hs : k ≤ S.card) (ht : k ≤ T.card) :
    h * k ≤ (D : K) ^ 2 * ((W \ (S ∪ T)).card + (Wᶜ.card : K)) := by
  have h1 : k ≤ min S.card Sᶜ.card * D := by
    rcases le_total S.card Sᶜ.card with hle | hle
    · rw [min_eq_left hle]
      exact hs.trans (Nat.le_mul_of_pos_right _ hD)
    · rw [min_eq_right hle]
      exact ht.trans (context_card_le hc hmin hdeg)
  have h2 := cut_le_missed hc hdeg
  have cover : (S ∪ T)ᶜ ⊆ (W \ (S ∪ T)) ∪ Wᶜ := by
    intro v hv
    by_cases hw : v ∈ W
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hw, Finset.mem_compl.mp hv⟩)
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hw)
  have h3 := (Finset.card_le_card cover).trans (Finset.card_union_le ..)
  have hd : 0 ≤ (D : K) := Nat.cast_nonneg D
  calc
    h * k ≤ h * ((min S.card Sᶜ.card : ℕ) * (D : K)) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast h1) hh
    _ = (h * (min S.card Sᶜ.card : ℕ)) * D := (mul_assoc ..).symm
    _ ≤ (cutSize G S : K) * D := mul_le_mul_of_nonneg_right (expand S) hd
    _ ≤ (((S ∪ T)ᶜ.card : K) * D) * D :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hd
    _ ≤ ((((W \ (S ∪ T)).card : K) + Wᶜ.card) * D) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast h3) hd) hd
    _ = _ := by ring

namespace Form

/-- Fix the variables outside W to a Boolean word with ones on F. -/
def restrict (p : Form V K) (W F : Finset V) : Form V K where
  coeff A := ∑ B : Finset V, if B ∩ W = A then (if B ⊆ W ∪ F then p.coeff B else 0) else 0
  nonneg A := Finset.sum_nonneg fun B _ => by
    by_cases he : B ∩ W = A <;> by_cases hb : B ⊆ W ∪ F <;> simp [he, hb, p.nonneg]

omit [Fintype V] in
private theorem restriction_test (W F X B : Finset V) (hd : Disjoint W F) :
    B ⊆ (X ∩ W) ∪ F ↔ B ⊆ W ∪ F ∧ B ∩ W ⊆ X := by
  constructor
  · intro h
    constructor
    · intro v hv
      rcases Finset.mem_union.mp (h hv) with hx | hf
      · exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).2
      · exact Finset.mem_union_right _ hf
    · intro v hv
      obtain ⟨hb, hw⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp (h hb) with hx | hf
      · exact (Finset.mem_inter.mp hx).1
      · exact False.elim (Finset.disjoint_left.mp hd hw hf)
  · rintro ⟨hs, hx⟩ v hv
    rcases Finset.mem_union.mp (hs hv) with hw | hf
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx (Finset.mem_inter.mpr ⟨hv, hw⟩), hw⟩)
    · exact Finset.mem_union_right _ hf

theorem value_restrict (p : Form V K) (W F X : Finset V) (hd : Disjoint W F) :
    (p.restrict W F).value X = p.value ((X ∩ W) ∪ F) := by
  classical
  calc
    _ = ∑ B : Finset V, ∑ A ∈ X.powerset,
        if B ∩ W = A then (if B ⊆ W ∪ F then p.coeff B else 0) else 0 := by
      unfold value restrict
      rw [Finset.sum_comm]
    _ = ∑ B : Finset V, if B ⊆ (X ∩ W) ∪ F then p.coeff B else 0 := by
      apply Finset.sum_congr rfl
      intro B _
      by_cases hB : B ⊆ W ∪ F <;> by_cases hW : B ∩ W ⊆ X <;>
        simp [Finset.sum_ite_eq, restriction_test W F X B hd, hB, hW]
    _ = _ := (value_sum _ _).symm

theorem restrict_pos (p : Form V K) (W F A : Finset V) :
    0 < (p.restrict W F).coeff A ↔ ∃ B, B ∩ W = A ∧ B ⊆ W ∪ F ∧ 0 < p.coeff B := by
  let w (B : Finset V) := if B ∩ W = A then (if B ⊆ W ∪ F then p.coeff B else 0) else 0
  have hw (B : Finset V) : 0 ≤ w B := by
    dsimp [w]
    by_cases he : B ∩ W = A <;> by_cases hb : B ⊆ W ∪ F <;> simp [he, hb, p.nonneg]
  change (0 < ∑ B : Finset V, w B) ↔ _
  rw [Finset.sum_pos_iff_of_nonneg fun B _ => hw B]
  constructor
  · rintro ⟨B, _, hb⟩
    by_cases he : B ∩ W = A <;> by_cases hs : B ⊆ W ∪ F <;> simp [w, he, hs] at hb
    exact ⟨B, he, hs, hb⟩
  · rintro ⟨B, he, hs, hb⟩
    exact ⟨B, Finset.mem_univ _, by simpa [w, he, hs] using hb⟩

end Form

/-- The monomial at each independent set has the same strictly positive
coefficient (three for the switched source CNF). -/
noncomputable def target (G : Graph V) (c : K) (hc : 0 < c) : Form V K := by
  classical
  exact ⟨fun A => if Independent G A then c else 0, fun A => by
    dsimp
    split <;> first | exact hc.le | exact le_rfl⟩

omit [Fintype V] [DecidableEq V] [IsStrictOrderedRing K] in
theorem target_pos (G : Graph V) (c : K) (hc : 0 < c) (A : Finset V) :
    0 < (target G c hc).coeff A ↔ Independent G A := by
  classical
  by_cases hi : Independent G A <;> simp [target, hi, hc]

theorem restricted_target_pos (G : Graph V) (c : K) (hc : 0 < c) (W F A : Finset V) :
    0 < ((target G c hc).restrict W F).coeff A ↔ A ⊆ W ∧ Independent G A := by
  rw [Form.restrict_pos]
  constructor
  · rintro ⟨B, rfl, _, hb⟩
    exact ⟨Finset.inter_subset_right, ((target_pos G c hc B).1 hb).mono Finset.inter_subset_left⟩
  · rintro ⟨hw, hi⟩
    exact ⟨A, Finset.inter_eq_left.mpr hw, hw.trans Finset.subset_union_left, (target_pos G c hc A).2 hi⟩

/-- The semantic premise compares only scalar output values on Boolean inputs.
Projecting the enabled set to W gives the usual pullback of a free-variable
circuit to the ambient vertex set. -/
def ComputesSlice (P : Program V K) (r : ℕ) (G : Graph V) (c : K) (hc : 0 < c)
    (W F : Finset V) : Prop :=
  ∀ X, scalar P X r = (target G c hc).value ((X ∩ W) ∪ F)

theorem terms_of_scalar_correctness {P : Program V K} {G : Graph V} {r : ℕ} {c : K}
    {hc : 0 < c} {W F : Finset V} (hd : Disjoint W F)
    (correct : ComputesSlice P r G c hc W F) (A : Finset V) :
    Term P r A ↔ A ⊆ W ∧ Independent G A := by
  have he (X : Finset V) : (forms P r).value X = ((target G c hc).restrict W F).value X := by
    rw [scalar_semantics, Form.value_restrict _ W F X hd]
    exact correct X
  unfold Term
  rw [Form.coeff_eq_of_values he, restricted_target_pos]

/-- The same missed set applies to all monomials routed through a fixed
register, independent of which occurrence is used. -/
noncomputable def missed (P : Program V K) (g r : ℕ) (W : Finset V) : Finset V :=
  W \ (gateVertices P g ∪ contextVertices P g r)

theorem avoids_missed {P : Program V K} {g r : ℕ} {A C : Finset V}
    (ha : Term P g A) (ctx : Context P g r C) (W : Finset V) :
    Disjoint (A ∪ C) (missed P g r W) := by
  apply Finset.disjoint_left.mpr
  intro v hv hm
  apply (Finset.mem_sdiff.mp hm).2
  rcases Finset.mem_union.mp hv with hv | hv
  · exact Finset.mem_union_left _ (gate_mem.mpr ⟨A, ha, hv⟩)
  · exact Finset.mem_union_right _ (context_mem.mpr ⟨C, ctx, hv⟩)

/-- Every large independent set of free vertices encounters a genuine
product register missing a large, fixed set of free vertices. -/
theorem balanced_product_separator {P : Program V K} {G : Graph V} {r k D : ℕ} {c h : K}
    {hc : 0 < c} {W F : Finset V} (hd : Disjoint W F) (correct : ComputesSlice P r G c hc W F)
    (small : SmallAtoms P r k) (hmin : ∀ v, (G.nbr v).Nonempty) (hD : 0 < D)
    (hdeg : ∀ v, (G.nbr v).card ≤ D) (hh : 0 ≤ h)
    (expand : ∀ U, h * (min U.card Uᶜ.card : ℕ) ≤ (cutSize G U : K))
    (U : Finset V) (hW : U ⊆ W) (hI : Independent G U) (large : 3 * k ≤ U.card) :
    ∃ g ≤ r, (∃ a b, P g = .mul a b) ∧ Disjoint U (missed P g r W) ∧
      h * k ≤ (D : K) ^ 2 * (((missed P g r W).card : K) + Wᶜ.card) := by
  have hu := (terms_of_scalar_correctness hd correct U).2 ⟨hW, hI⟩
  obtain ⟨g, A, C, op, hA, ha, hb, ctx, he⟩ :=
    balanced_occurrence small (le_refl r) hu (by omega)
  have hcs : k ≤ C.card := by
    have hcu := Finset.card_union_le A C
    rw [he] at hcu
    omega
  have hs : k ≤ (gateVertices P g).card :=
    ha.trans (Finset.card_le_card fun v hv => gate_mem.mpr ⟨A, hA, hv⟩)
  have ht : k ≤ (contextVertices P g r).card :=
    hcs.trans (Finset.card_le_card fun v hv => context_mem.mpr ⟨C, ctx, hv⟩)
  have hcross := gate_context_no_cross (fun B hB => ((terms_of_scalar_correctness hd correct B).1 hB).2) g
  exact ⟨g, ctx.hole_le, op, he ▸ avoids_missed hA ctx W,
    missed_vertices hcross hmin hD hdeg hh expand hs ht⟩

/-- Independent vertex sets using only W. All probabilities below can
therefore be expressed by finite cardinalities. -/
noncomputable def indSets (G : Graph V) (W : Finset V) : Finset (Finset V) := by
  classical exact W.powerset.filter (Independent G)

omit [Fintype V] [DecidableEq V] in
theorem mem_indSets {G : Graph V} {W I : Finset V} :
    I ∈ indSets G W ↔ I ⊆ W ∧ Independent G I := by
  classical simp [indSets]

omit [Fintype V] [DecidableEq V] in
theorem indSets_pos (G : Graph V) (W : Finset V) : 0 < (indSets G W).card := by
  apply Finset.card_pos.mpr
  exact ⟨∅, mem_indSets.mpr ⟨Finset.empty_subset _, fun _ h => False.elim (Finset.notMem_empty _ h)⟩⟩

noncomputable def containing (G : Graph V) (W : Finset V) (v : V) : Finset (Finset V) :=
  (indSets G W).filter fun I => v ∈ I

omit [Fintype V] in
theorem partition_at (G : Graph V) (W : Finset V) (v : V) :
    (containing G W v).card + (indSets G (W.erase v)).card = (indSets G W).card := by
  classical
  have e : indSets G (W.erase v) = (indSets G W).filter fun I => v ∉ I := by
    ext I
    simp only [mem_indSets, Finset.mem_filter, Finset.subset_erase]
    tauto
  rw [e]
  apply Finset.filter_card_add_filter_neg_card_eq_card

omit [Fintype V] in
private theorem independent_insert {G : Graph V} {I : Finset V} (h : Independent G I) (v : V) :
    Independent G (insert v (I \ G.nbr v)) := by
  intro x hx y hy
  rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
  · exact G.loopless _
  · exact fun he => (Finset.mem_sdiff.mp hy).2 (G.symm he)
  · exact (Finset.mem_sdiff.mp hx).2
  · exact h _ (Finset.mem_sdiff.mp hx).1 _ (Finset.mem_sdiff.mp hy).1

omit [Fintype V] in
/-- The omitted neighbors record all the information lost on inserting v. -/
theorem insertion_bound (G : Graph V) (W : Finset V) {v : V} (hv : v ∈ W)
    {D : ℕ} (hdeg : (G.nbr v).card ≤ D) :
    (indSets G (W.erase v)).card ≤ (containing G W v).card * 2 ^ D := by
  classical
  let pack (I : Finset V) := (insert v (I \ G.nbr v), I ∩ G.nbr v)
  let unpack (p : Finset V × Finset V) := p.1.erase v ∪ p.2
  have leftInv (I : Finset V) (hi : I ∈ indSets G (W.erase v)) : unpack (pack I) = I := by
    obtain ⟨_, ho⟩ := Finset.subset_erase.mp (mem_indSets.mp hi).1
    have hn : v ∉ I \ G.nbr v := fun hm => ho (Finset.mem_sdiff.mp hm).1
    simp [unpack, pack, Finset.erase_insert hn, Finset.sdiff_union_inter]
  have mapsto : Set.MapsTo pack (indSets G (W.erase v))
      ((containing G W v) ×ˢ (G.nbr v).powerset : Finset _) := by
    intro I hI
    obtain ⟨hw, hi⟩ := mem_indSets.mp hI
    have hs : I ⊆ W := (Finset.subset_erase.mp hw).1
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨mem_indSets.mpr ⟨Finset.insert_subset hv (Finset.sdiff_subset.trans hs),
        independent_insert hi v⟩, Finset.mem_insert_self ..⟩
    · exact Finset.mem_powerset.mpr Finset.inter_subset_right
  have inject : Set.InjOn pack (indSets G (W.erase v)) := by
    intro I hI J hJ he
    exact (leftInv I hI).symm.trans ((congrArg unpack he).trans (leftInv J hJ))
  calc
    _ ≤ ((containing G W v) ×ˢ (G.nbr v).powerset).card := Finset.card_le_card_of_injOn pack mapsto inject
    _ = (containing G W v).card * 2 ^ (G.nbr v).card := by simp
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hdeg)

/-- Lower inclusion probability and upper exclusion probability for a
uniformly random independent set on any induced vertex set. -/
def delta (K : Type*) [Field K] (D : ℕ) : K := 1 / ((2 : K) ^ D + 1)
def rho (K : Type*) [Field K] (D : ℕ) : K := (2 : K) ^ D / ((2 : K) ^ D + 1)

theorem rho_bounds (D : ℕ) : 0 < rho K D ∧ rho K D < 1 := by
  have hp : 0 < (2 : K)^D := pow_pos (by norm_num) _
  constructor
  · exact div_pos hp (by linarith)
  · change (2 : K) ^ D / (_ + 1) < 1
    apply (div_lt_iff₀ (by linarith : 0 < (2 : K)^D + 1)).mpr
    linarith

omit [Fintype V] in
theorem inclusion_exclusion (G : Graph V) (W : Finset V) {v : V} (hv : v ∈ W)
    {D : ℕ} (hdeg : (G.nbr v).card ≤ D) :
    delta K D * (indSets G W).card ≤ (containing G W v).card ∧
      ((indSets G (W.erase v)).card : K) ≤ rho K D * (indSets G W).card := by
  have hp : 0 < (2 : K)^D + 1 := by positivity
  have hins : ((indSets G (W.erase v)).card : K) ≤ (containing G W v).card * (2 : K) ^ D := by
    exact_mod_cast insertion_bound G W hv hdeg
  have hparts : ((containing G W v).card : K) + (indSets G (W.erase v)).card = (indSets G W).card := by
    exact_mod_cast partition_at G W v
  constructor
  · rw [delta, div_mul_eq_mul_div, div_le_iff₀ hp]
    rw [← hparts]
    linarith only [hins]
  · rw [rho, div_mul_eq_mul_div, le_div_iff₀ hp, ← hparts]
    linarith only [hins]

omit [Fintype V] in
/-- Iterating the vertex bound on successively smaller induced subgraphs. -/
theorem avoidance (G : Graph V) (W B : Finset V) (hB : B ⊆ W) {D : ℕ}
    (hdeg : ∀ v, (G.nbr v).card ≤ D) :
    ((indSets G (W \ B)).card : K) ≤ rho K D ^ B.card * (indSets G W).card := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert v B hv ih =>
    have hW : B ⊆ W := Finset.Subset.trans (Finset.subset_insert _ _) hB
    have hvW : v ∈ W \ B := Finset.mem_sdiff.mpr ⟨hB (Finset.mem_insert_self ..), hv⟩
    have he : W \ insert v B = (W \ B).erase v := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      tauto
    rw [he, Finset.card_insert_of_notMem hv, pow_succ']
    calc
      _ ≤ rho K D * (indSets G (W \ B)).card := (inclusion_exclusion G _ hvW (hdeg v)).2
      _ ≤ rho K D * (rho K D ^ B.card * (indSets G W).card) :=
        mul_le_mul_of_nonneg_left (ih hW) (rho_bounds D).1.le
      _ = _ := (mul_assoc ..).symm

noncomputable def largeSets (G : Graph V) (W : Finset V) (k : ℕ) : Finset (Finset V) :=
  (indSets G W).filter fun I => 3 * k ≤ I.card

omit [Fintype V] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem count_memberships (G : Graph V) (W : Finset V) :
    (∑ I ∈ indSets G W, (I.card : K)) = ∑ v ∈ W, ((containing G W v).card : K) := by
  classical
  calc
    _ = ∑ I ∈ indSets G W, ∑ v ∈ W, if v ∈ I then (1 : K) else 0 := by
      apply Finset.sum_congr rfl
      intro I hI
      have hs : W.filter (· ∈ I) = I := by
        ext v
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun h => ⟨(mem_indSets.mp hI).1 h, h⟩⟩
      rw [Finset.sum_boole, hs]
    _ = _ := by rw [Finset.sum_comm]; simp [containing]

omit [Fintype V] in
theorem independent_size_sum (G : Graph V) (W : Finset V) {D : ℕ}
    (hdeg : ∀ v, (G.nbr v).card ≤ D) :
    (W.card : K) * (delta K D * (indSets G W).card) ≤ ∑ I ∈ indSets G W, (I.card : K) := by
  rw [count_memberships]
  calc
    _ = ∑ _v ∈ W, delta K D * (indSets G W).card := by simp
    _ ≤ _ := Finset.sum_le_sum fun v hv => (inclusion_exclusion G W hv (hdeg v)).1

omit [Fintype V] [DecidableEq V] in
private theorem large_tail (G : Graph V) (W : Finset V) (k : ℕ) :
    (∑ I ∈ indSets G W, (I.card : K)) ≤
      (indSets G W).card * ((3 : K) * k) + (largeSets G W k).card * (W.card : K) := by
  classical
  calc
    _ ≤ ∑ I ∈ indSets G W, ((3 : K)*k + if 3*k ≤ I.card then (W.card : K) else 0) := by
      apply Finset.sum_le_sum
      intro I hI
      by_cases hb : 3*k ≤ I.card
      · rw [if_pos hb]
        have hs : (I.card : K) ≤ W.card := by exact_mod_cast Finset.card_le_card (mem_indSets.mp hI).1
        have hk : 0 ≤ (k : K) := Nat.cast_nonneg k
        linarith
      · rw [if_neg hb, add_zero]
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hb))
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [largeSets]

omit [Fintype V] in
/-- Quantitative first-moment estimate on the same free-vertex family. -/
theorem large_fraction (G : Graph V) (W : Finset V) (hW : W.Nonempty) {k D : ℕ}
    (hdeg : ∀ v, (G.nbr v).card ≤ D) (threshold : (6 : K)*k ≤ delta K D * W.card) :
    delta K D / 2 * (indSets G W).card ≤ (largeSets G W k).card := by
  have hm := (independent_size_sum (K := K) G W hdeg).trans (large_tail G W k)
  have hn := mul_le_mul_of_nonneg_right threshold (Nat.cast_nonneg (α := K) (indSets G W).card)
  have hwp : 0 < (W.card : K) := by exact_mod_cast Finset.card_pos.mpr hW
  apply le_of_mul_le_mul_of_pos_left (a := (W.card : K)) _ hwp
  linarith only [hm, hn]

/-- Distinct multiplication registers in the actual finite program prefix. -/
noncomputable def productRegisters (P : Program V K) (r : ℕ) : Finset ℕ := by
  classical exact (Finset.range (r+1)).filter fun g => ∃ a b, P g = .mul a b

/-- A finite union bound over register IDs, after the same omission event
has been shown to apply to every routed monomial for that register. -/
private theorem cover_bound {P : Program V K} {G : Graph V} {W : Finset V} {r k m D : ℕ}
    (hdeg : ∀ v, (G.nbr v).card ≤ D)
    (route : ∀ U ∈ largeSets G W k, ∃ g ∈ productRegisters P r,
      Disjoint U (missed P g r W) ∧ m ≤ (missed P g r W).card) :
    ((largeSets G W k).card : K) ≤ (productRegisters P r).card *
      (rho K D ^ m * (indSets G W).card) := by
  classical
  let good := (productRegisters P r).filter fun g => m ≤ (missed P g r W).card
  let avoided (g : ℕ) := indSets G (W \ missed P g r W)
  have cover : largeSets G W k ⊆ good.biUnion avoided := by
    intro U hu
    obtain ⟨g, hreg, hdis, hsz⟩ := route U hu
    obtain ⟨hs, hi⟩ := mem_indSets.mp (Finset.mem_filter.mp hu).1
    refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨hreg, hsz⟩, mem_indSets.mpr ⟨?_, hi⟩⟩
    exact fun v hv => Finset.mem_sdiff.mpr ⟨hs hv, Finset.disjoint_left.mp hdis hv⟩
  have hc (g : ℕ) (hg : g ∈ good) :
      ((avoided g).card : K) ≤ rho K D ^ m * (indSets G W).card := by
    have hnon := (rho_bounds (K := K) D).1.le
    have hmon := (rho_bounds (K := K) D).2.le
    have hpow := pow_le_pow_of_le_one hnon hmon (Finset.mem_filter.mp hg).2
    exact (avoidance G W _ Finset.sdiff_subset hdeg).trans
      (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ g ∈ good, ((avoided g).card : K) := by
      exact_mod_cast (Finset.card_le_card cover).trans Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ good, rho K D ^ m * (indSets G W).card := Finset.sum_le_sum hc
    _ = good.card * (rho K D ^ m * (indSets G W).card) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ (productRegisters P r)))
      (mul_nonneg (pow_nonneg (rho_bounds D).1.le _) (Nat.cast_nonneg _))

/-- Finite exponential lower bound for the full positive arithmetic DAG.
The only functional premise is exact scalar agreement on Boolean inputs.
Here k is the atom-degree threshold, m is an integer omission margin, and
W is the set of free switches. The denominator decays exponentially in m. -/
theorem finite_product_gate_bound {P : Program V K} {G : Graph V} {r k m D : ℕ} {c h : K}
    {hc : 0 < c} {W F : Finset V} (hd : Disjoint W F) (correct : ComputesSlice P r G c hc W F)
    (small : SmallAtoms P r k) (hmin : ∀ v, (G.nbr v).Nonempty) (hD : 0 < D)
    (hdeg : ∀ v, (G.nbr v).card ≤ D) (hh : 0 ≤ h)
    (expand : ∀ U, h * (min U.card Uᶜ.card : ℕ) ≤ (cutSize G U : K))
    (hW : W.Nonempty) (threshold : (6 : K)*k ≤ delta K D * W.card)
    (margin : (D : K)^2 * ((m : K) + Wᶜ.card) ≤ h*k) :
    delta K D / (2 * rho K D ^ m) ≤ ((productRegisters P r).card : K) := by
  classical
  have route (U : Finset V) (hu : U ∈ largeSets G W k) : ∃ g ∈ productRegisters P r,
      Disjoint U (missed P g r W) ∧ m ≤ (missed P g r W).card := by
    obtain ⟨hI, hlarge⟩ := Finset.mem_filter.mp hu
    obtain ⟨hsub, hind⟩ := mem_indSets.mp hI
    obtain ⟨g, hgr, hgate, hdis, hmiss⟩ :=
      balanced_product_separator hd correct small hmin hD hdeg hh expand U hsub hind hlarge
    have hDp : 0 < (D : K) := by exact_mod_cast hD
    have hm := le_of_mul_le_mul_of_pos_left (margin.trans hmiss) (pow_pos hDp 2)
    have hsz : (m : K) ≤ (missed P g r W).card := by linarith only [hm]
    exact ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hgate⟩, hdis, by exact_mod_cast hsz⟩
  have hl := (large_fraction G W hW hdeg threshold).trans (cover_bound hdeg route)
  have hpos : 0 < ((indSets G W).card : K) := by exact_mod_cast indSets_pos G W
  rw [← mul_assoc] at hl
  have hbound := le_of_mul_le_mul_of_pos_right hl hpos
  have hr := pow_pos (rho_bounds (K := K) D).1 m
  apply (div_le_iff₀ (mul_pos zero_lt_two hr)).mpr
  linarith only [hbound]

/-- Specializing the program at a Boolean partial assignment changes only
its input coefficient tables. -/
def specialize (P : Program V K) (W F : Finset V) (i : ℕ) : Gate V K i :=
  match P i with
  | .atom p => .atom (p.restrict W F)
  | .add a b => .add a b
  | .mul a b => .mul a b

theorem scalar_specialize (P : Program V K) (W F : Finset V) (hd : Disjoint W F)
    (X : Finset V) (i : ℕ) :
    scalar (specialize P W F) X i = scalar P ((X ∩ W) ∪ F) i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    conv_lhs => rw [scalar]
    conv_rhs => rw [scalar]
    unfold specialize
    cases hop : P i with
    | atom p => exact Form.value_restrict p W F X hd
    | add a b => exact congrArg₂ (· + ·) (ih a a.isLt) (ih b b.isLt)
    | mul a b => exact congrArg₂ (· * ·) (ih a a.isLt) (ih b b.isLt)

theorem registers_specialize (P : Program V K) (W F : Finset V) (r : ℕ) :
    productRegisters (specialize P W F) r = productRegisters P r := by
  classical
  ext i
  simp only [productRegisters, Finset.mem_filter]
  apply and_congr_right
  intro _
  cases hop : P i <;> simp [specialize, hop]

/-- This is the monomial-size hypothesis after fixing the switches. -/
def SmallSliceAtoms (P : Program V K) (W F : Finset V) (r k : ℕ) : Prop :=
  ∀ i ≤ r, ∀ p, P i = .atom p → ∀ A, 0 < (p.restrict W F).coeff A → A.card < k

theorem small_specialize {P : Program V K} {W F : Finset V} {r k : ℕ}
    (h : SmallSliceAtoms P W F r k) : SmallAtoms (specialize P W F) r k := by
  intro i hi p hp A hA
  cases hop : P i with
  | atom q =>
    have he : q.restrict W F = p := by simpa [specialize, hop] using hp
    exact h i hi q hop A (he ▸ hA)
  | add a b => simp [specialize, hop] at hp
  | mul a b => simp [specialize, hop] at hp

theorem small_slice_of_small {P : Program V K} {r k : ℕ} (h : SmallAtoms P r k) (W F : Finset V) :
    SmallSliceAtoms P W F r k := by
  intro i hi p hp A hA
  obtain ⟨B, rfl, _, hb⟩ := (Form.restrict_pos p W F A).1 hA
  exact lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_left) (h i hi p hp B hb)

/-- The original circuit is required to agree with the target only on the
specified subcube. Both the answer and the gate count refer to that same
original circuit. The local degree condition is on its specialized atoms. -/
theorem finite_subcube_gate_bound {P : Program V K} {G : Graph V} {r k m D : ℕ} {c h : K}
    {hc : 0 < c} {W F : Finset V} (hd : Disjoint W F)
    (correct : ∀ X ⊆ W, scalar P (X ∪ F) r = (target G c hc).value (X ∪ F))
    (small : SmallSliceAtoms P W F r k) (hmin : ∀ v, (G.nbr v).Nonempty) (hD : 0 < D)
    (hdeg : ∀ v, (G.nbr v).card ≤ D) (hh : 0 ≤ h)
    (expand : ∀ U, h * (min U.card Uᶜ.card : ℕ) ≤ (cutSize G U : K))
    (hW : W.Nonempty) (threshold : (6 : K)*k ≤ delta K D * W.card)
    (margin : (D : K)^2 * ((m : K) + Wᶜ.card) ≤ h*k) :
    delta K D / (2 * rho K D ^ m) ≤ ((productRegisters P r).card : K) := by
  have he : ComputesSlice (specialize P W F) r G c hc W F := by
    intro X
    exact (scalar_specialize P W F hd X r).trans (correct _ Finset.inter_subset_right)
  have hb := finite_product_gate_bound hd he (small_specialize small) hmin hD hdeg hh expand hW threshold margin
  rwa [registers_specialize] at hb

omit [Fintype V] [DecidableEq V] [IsStrictOrderedRing K] in
/-- Evaluating the count target returns the actual number of enabled
independent sets times its prefactor. -/
theorem target_value_card (G : Graph V) (c : K) (hc : 0 < c) (X : Finset V) :
    (target G c hc).value X = c * (indSets G X).card := by
  classical
  change (∑ A ∈ X.powerset, if Independent G A then c else 0) = _
  rw [← Finset.sum_filter]
  simp [indSets, mul_comm]

/-- With reduce = id this evaluates the natural-number lift. With
reduce n = n % M every scalar gate uses a modular register. -/
def natRegisters (P : Program V K) (read : ℕ → Finset V → ℕ) (reduce : ℕ → ℕ)
    (X : Finset V) (i : ℕ) : ℕ :=
  match P i with
  | .atom _ => reduce (read i X)
  | .add a b => reduce (natRegisters P read reduce X a.val + natRegisters P read reduce X b.val)
  | .mul a b => reduce (natRegisters P read reduce X a.val * natRegisters P read reduce X b.val)
termination_by i
decreasing_by all_goals first | exact a.isLt | exact b.isLt

omit [Fintype V] [DecidableEq V] [IsStrictOrderedRing K] in
theorem registers_mod (P : Program V K) (read : ℕ → Finset V → ℕ) (M : ℕ) (X : Finset V) (i : ℕ) :
    natRegisters P read (· % M) X i = natRegisters P read id X i % M := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    conv_lhs => rw [natRegisters]
    conv_rhs => rw [natRegisters]
    cases P i with
    | atom p => rfl
    | add a b =>
      exact (congrArg (· % M) (congrArg₂ (· + ·) (ih a a.isLt) (ih b b.isLt))).trans
        (Nat.add_mod ..).symm
    | mul a b =>
      exact (congrArg (· % M) (congrArg₂ (· * ·) (ih a a.isLt) (ih b b.isLt))).trans
        (Nat.mul_mod ..).symm

omit [Fintype V] [DecidableEq V] [IsStrictOrderedRing K] in
private theorem cast_lift {P : Program V K} {read : ℕ → Finset V → ℕ} {r : ℕ} {X : Finset V}
    (integerAtoms : ∀ j ≤ r, ∀ p, P j = .atom p → (read j X : K) = p.value X)
    (i : ℕ) (hi : i ≤ r) : (natRegisters P read id X i : K) = scalar P X i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    conv_lhs => rw [natRegisters]
    conv_rhs => rw [scalar]
    cases hop : P i with
    | atom p => exact integerAtoms i hi p hop
    | add a b =>
      exact (Nat.cast_add ..).trans (congrArg₂ (· + ·) (ih a a.isLt (a.isLt.le.trans hi)) (ih b b.isLt (b.isLt.le.trans hi)))
    | mul a b =>
      exact (Nat.cast_mul ..).trans (congrArg₂ (· * ·) (ih a a.isLt (a.isLt.le.trans hi)) (ih b b.isLt (b.isLt.le.trans hi)))

/-- Section F4's strict no-wrap condition. Modular arithmetic is actually
performed at every binary gate. Only the two final natural values must be
strictly below M. Each atom has an integer lift agreeing with its positive
coefficient-table value on the selected subcube. -/
theorem finite_modular_gate_bound {P : Program V K} {G : Graph V} {r k m D M t : ℕ} {h : K}
    {W F : Finset V} (ht : 0 < t) (hd : Disjoint W F) (read : ℕ → Finset V → ℕ)
    (integerAtoms : ∀ i ≤ r, ∀ p, P i = .atom p → ∀ X ⊆ W, (read i (X ∪ F) : K) = p.value (X ∪ F))
    (correct : ∀ X ⊆ W, natRegisters P read (· % M) (X ∪ F) r = (t * (indSets G (X ∪ F)).card) % M)
    (noWrap : ∀ X ⊆ W, natRegisters P read id (X ∪ F) r < M ∧ t * (indSets G (X ∪ F)).card < M)
    (small : SmallSliceAtoms P W F r k) (hmin : ∀ v, (G.nbr v).Nonempty) (hD : 0 < D)
    (hdeg : ∀ v, (G.nbr v).card ≤ D) (hh : 0 ≤ h)
    (expand : ∀ U, h * (min U.card Uᶜ.card : ℕ) ≤ (cutSize G U : K))
    (hW : W.Nonempty) (threshold : (6 : K)*k ≤ delta K D * W.card)
    (margin : (D : K)^2 * ((m : K) + Wᶜ.card) ≤ h*k) :
    delta K D / (2 * rho K D ^ m) ≤ ((productRegisters P r).card : K) := by
  have hc : 0 < (t : K) := by exact_mod_cast ht
  apply finite_subcube_gate_bound (c := (t : K)) (hc := hc) hd _ small hmin hD hdeg hh expand hW threshold margin
  intro X hX
  have hw := correct X hX
  obtain ⟨hLo, hT⟩ := noWrap X hX
  rw [registers_mod, Nat.mod_eq_of_lt hLo, Nat.mod_eq_of_lt hT] at hw
  have lift := cast_lift (fun i hi p hp => integerAtoms i hi p hp X hX) r (le_refl r)
  rw [← lift, hw, Nat.cast_mul, target_value_card]

#print axioms Form.value_product
#print axioms Form.product_pos
#print axioms Form.coeff_eq_of_values
#print axioms scalar_semantics
#print axioms Context.fill
#print axioms balanced_occurrence
#print axioms gate_context_no_cross
#print axioms context_card_le
#print axioms cut_le_missed
#print axioms missed_vertices
#print axioms Form.value_restrict
#print axioms restricted_target_pos
#print axioms terms_of_scalar_correctness
#print axioms avoids_missed
#print axioms balanced_product_separator
#print axioms insertion_bound
#print axioms rho_bounds
#print axioms inclusion_exclusion
#print axioms avoidance
#print axioms independent_size_sum
#print axioms large_fraction
#print axioms finite_product_gate_bound

#print axioms scalar_specialize
#print axioms registers_specialize
#print axioms small_slice_of_small
#print axioms finite_subcube_gate_bound

#print axioms target_value_card
#print axioms registers_mod
#print axioms finite_modular_gate_bound

end PositiveSupport
