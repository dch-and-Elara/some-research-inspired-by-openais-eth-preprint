import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-! Exact combinatorial upper bound for diagonal pins under a per-cell
incidence cap. This bound does not assume the label distribution is random. -/
namespace DiagonalOptimal
open scoped BigOperators
universe u v w

abbrev Word (I : Type u) (S : Type v) := I → S
abbrev Cell (I : Type u) (S : Type v) := Word I S × Word I S

variable {I : Type u} {S : Type v}

def diagonalEmbedding : Word I S ↪ Cell I S where
  toFun x := (x,x)
  inj' _ _ h := congrArg Prod.fst h

def diagonalCells [Fintype I] [DecidableEq I] [Fintype S] : Finset (Cell I S) :=
  Finset.univ.map diagonalEmbedding

theorem mem_diagonalCells [Fintype I] [DecidableEq I] [Fintype S] (a : Cell I S) :
    a ∈ diagonalCells ↔ a.1 = a.2 := by
  classical
  constructor
  · intro h
    obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp h
    rfl
  · intro h
    exact Finset.mem_map.mpr ⟨a.1,Finset.mem_univ _,Prod.ext rfl h⟩

theorem card_diagonalCells [Fintype I] [DecidableEq I] [Fintype S] :
    (diagonalCells (I := I) (S := S)).card = (Fintype.card S) ^ Fintype.card I := by
  simp [diagonalCells]

/-- A fixed symbol leaves a free word on all other coordinates. -/
def extendAt [DecidableEq I] (t : I) (g : S) (w : {i // i ≠ t} → S) : Word I S :=
  fun i => if h : i = t then g else w ⟨i,h⟩

def fixedEmbedding [DecidableEq I] (t : I) (g : S) :
    ({i // i ≠ t} → S) ↪ Cell I S where
  toFun w := (extendAt t g w, extendAt t g w)
  inj' x y h := by
    funext i
    have hs := congrFun (congrArg Prod.fst h) i.1
    simpa [extendAt,i.2] using hs

def groupDiagonalCells [Fintype I] [DecidableEq I] [Fintype S]
    (t : I) (g : S) : Finset (Cell I S) :=
  Finset.univ.map (fixedEmbedding t g)

theorem mem_groupDiagonalCells [Fintype I] [DecidableEq I] [Fintype S]
    (t : I) (g : S) (a : Cell I S) :
    a ∈ groupDiagonalCells t g ↔ a.1 = a.2 ∧ a.1 t = g := by
  classical
  constructor
  · intro ha
    obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp ha
    exact ⟨rfl,by simp [fixedEmbedding,extendAt]⟩
  · rintro ⟨h,ht⟩
    have he : extendAt t g (fun i => a.1 i.1) = a.1 := by
      funext i
      by_cases hi : i = t
      · subst i
        simp [extendAt,ht]
      · simp [extendAt,hi]
    exact Finset.mem_map.mpr ⟨fun i => a.1 i.1,Finset.mem_univ _,Prod.ext he (he.trans h)⟩

theorem card_groupDiagonalCells_free [Fintype I] [DecidableEq I] [Fintype S]
    (t : I) (g : S) :
    (groupDiagonalCells t g).card = Fintype.card ({i // i ≠ t} → S) := by
  simp [groupDiagonalCells]

theorem card_word_split [Fintype I] [DecidableEq I] [Fintype S] (t : I) :
    Fintype.card (Word I S) = Fintype.card S * Fintype.card ({i // i ≠ t} → S) := by
  simpa only [Fintype.card_prod] using Fintype.card_congr (Equiv.funSplitAt t S)

/-- Exactly K/r cells of a diagonal have a fixed symbol at one coordinate. -/
theorem card_groupDiagonalCells [Fintype I] [DecidableEq I] [Fintype S]
    (t : I) (g : S) :
    (groupDiagonalCells t g).card = ((Fintype.card S) ^ Fintype.card I) / Fintype.card S := by
  letI : Nonempty S := ⟨g⟩
  rw [card_groupDiagonalCells_free,← Fintype.card_fun (α := I) (β := S), card_word_split t]
  exact (Nat.mul_div_cancel_left _ Fintype.card_pos).symm

variable {P : Type w}

/-- Exact fibre count, followed by its uniform per-cell cap (rational
caps need not be rounded in the statement). -/
theorem load_budget {C : Type*} [DecidableEq C]
    (pins : Finset P) (label : P → C) (cells : Finset C) (cap : ℚ)
    (hcap : ∀ u ∈ cells, ((pins.filter fun p => label p = u).card : ℚ) ≤ cap) :
    ((pins.filter fun p => label p ∈ cells).card : ℚ) ≤ cap * (cells.card : ℚ) := by
  have hc := Finset.sum_card_fiberwise_eq_card_filter pins cells label
  rw [← hc, Nat.cast_sum]
  simpa [nsmul_eq_mul,mul_comm] using
    (Finset.sum_le_sum hcap :
      (∑ u ∈ cells, ((pins.filter fun p => label p = u).card : ℚ)) ≤ ∑ _u ∈ cells, cap)

/-- At most cap·K diagonal pins over all cell labels. -/
theorem diagonal_pin_cap [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (pins : Finset P) (label : P → Cell I S) (cap : ℚ)
    (hcap : ∀ u, ((pins.filter fun p => label p = u).card : ℚ) ≤ cap) :
    ((pins.filter fun p => (label p).1 = (label p).2).card : ℚ) ≤
      cap * (((Fintype.card S) ^ Fintype.card I : ℕ) : ℚ) := by
  have h := load_budget pins label diagonalCells cap (fun u _ => hcap u)
  simpa only [mem_diagonalCells,card_diagonalCells] using h

/-- At most cap·(K/r) diagonals in any specified group. -/
theorem group_diagonal_pin_cap [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (pins : Finset P) (label : P → Cell I S) (cap : ℚ)
    (hcap : ∀ u, ((pins.filter fun p => label p = u).card : ℚ) ≤ cap)
    (t : I) (g : S) :
    ((pins.filter fun p => (label p).1 = (label p).2 ∧ (label p).1 t = g).card : ℚ) ≤
      cap * (((Fintype.card S) ^ Fintype.card I / Fintype.card S : ℕ) : ℚ) := by
  have h := load_budget pins label (groupDiagonalCells t g) cap (fun u _ => hcap u)
  simpa only [mem_groupDiagonalCells,card_groupDiagonalCells] using h

#print axioms mem_diagonalCells
#print axioms mem_groupDiagonalCells
#print axioms card_diagonalCells
#print axioms card_groupDiagonalCells
#print axioms load_budget
#print axioms diagonal_pin_cap
#print axioms group_diagonal_pin_cap


/-- A pin's chosen physical incidence slot is injective in the slot index.
A per-cell bound on all incidences thus bounds the pins in that cell. -/
theorem pin_load_le_incidence_load {A C : Type*} [DecidableEq C]
    (pins : Finset P) (incidences : Finset A) (slot : P ↪ A)
    (comesFrom : ∀ p ∈ pins, slot p ∈ incidences) (label : A → C) (c : C) :
    (pins.filter fun p => label (slot p) = c).card ≤
      (incidences.filter fun a => label a = c).card := by
  calc
    _ = ((pins.filter fun p => label (slot p) = c).map slot).card := by simp
    _ ≤ _ := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨hp',hl⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨comesFrom p hp',hl⟩

theorem diagonal_cap_from_source {A : Type*} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (pins : Finset P) (incidences : Finset A) (slot : P ↪ A)
    (comesFrom : ∀ p ∈ pins, slot p ∈ incidences)
    (label : A → Cell I S) (cap : ℚ)
    (hcap : ∀ u, ((incidences.filter fun a => label a = u).card : ℚ) ≤ cap) :
    ((pins.filter fun p => (label (slot p)).1 = (label (slot p)).2).card : ℚ) ≤
      cap * (((Fintype.card S) ^ Fintype.card I : ℕ) : ℚ) := by
  apply diagonal_pin_cap pins (fun p => label (slot p)) cap
  intro c
  exact le_trans (by exact_mod_cast pin_load_le_incidence_load pins incidences slot comesFrom label c)
    (hcap c)

theorem group_diagonal_cap_from_source {A : Type*} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (pins : Finset P) (incidences : Finset A) (slot : P ↪ A)
    (comesFrom : ∀ p ∈ pins, slot p ∈ incidences)
    (label : A → Cell I S) (cap : ℚ)
    (hcap : ∀ u, ((incidences.filter fun a => label a = u).card : ℚ) ≤ cap)
    (t : I) (g : S) :
    ((pins.filter fun p => (label (slot p)).1 = (label (slot p)).2 ∧
      (label (slot p)).1 t = g).card : ℚ) ≤
      cap * (((Fintype.card S) ^ Fintype.card I / Fintype.card S : ℕ) : ℚ) := by
  apply group_diagonal_pin_cap pins (fun p => label (slot p)) cap _ t g
  intro c
  exact le_trans (by exact_mod_cast pin_load_le_incidence_load pins incidences slot comesFrom label c)
    (hcap c)

#print axioms pin_load_le_incidence_load
#print axioms diagonal_cap_from_source
#print axioms group_diagonal_cap_from_source

end DiagonalOptimal
