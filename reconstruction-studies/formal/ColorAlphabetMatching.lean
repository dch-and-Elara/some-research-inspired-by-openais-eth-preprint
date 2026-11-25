import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

namespace Reconstruction.ColorAlphabet

/-- The finite vertices of a round-robin schedule. -/
abbrev Round (n : ℕ) := ZMod (2 * n + 1)

/-- The even schedule includes the vertex at infinity. The odd schedule drops it. -/
abbrev Letters (n : ℕ) (even : Bool) :=
  {a : Option (Round n) // even = true ∨ a.isSome}

def letterIndex {n : ℕ} {even : Bool} (a : Letters n even) : ℕ :=
  a.val.elim (2*n+1) ZMod.val

theorem letterIndex_injective {n : ℕ} {even : Bool} :
    Function.Injective (@letterIndex n even) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  apply Subtype.ext
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have he : 2*n+1 = b.val := h
      have hb := b.val_lt
      omega
  | some a =>
    cases b with
    | none =>
      have he : a.val = 2*n+1 := h
      have ha := a.val_lt
      omega
    | some b => exact congrArg some (ZMod.val_injective _ h)

theorem letters_card (n : ℕ) (even : Bool) :
    Fintype.card (Letters n even) = 2*n+1 + if even then 1 else 0 := by
  cases even
  · let e : Round n ≃ Letters n false :=
      { toFun := fun a => ⟨some a, by simp⟩
        invFun := fun a => a.val.get (by simpa using a.property)
        left_inv := fun _ => rfl
        right_inv := by
          rintro ⟨a, ha⟩
          cases a <;> simp_all }
    rw [← Fintype.card_congr e, ZMod.card]
    simp
  · let e : Option (Round n) ≃ Letters n true :=
      { toFun := fun a => ⟨a, Or.inl rfl⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Fintype.card_congr e, Fintype.card_option, ZMod.card]
    rfl

private theorem twice_half (n : ℕ) : (2 : Round n) * ((n + 1 : ℕ) : Round n) = 1 := by
  have h : ((2 * n + 1 : ℕ) : Round n) = 0 := ZMod.natCast_self _
  push_cast at h ⊢
  linear_combination h

private def midpoint {n : ℕ} (a b : Round n) : Round n :=
  ((n + 1 : ℕ) : Round n) * (a + b)

private theorem double_midpoint {n : ℕ} (a b : Round n) :
    (2 : Round n) * midpoint a b = a + b := by
  rw [midpoint, ← mul_assoc, twice_half, one_mul]

/-- An edge between finite vertices belongs to the round of its midpoint. The
edge from infinity to a finite vertex belongs to that vertex's round. -/
def edgeRound {n : ℕ} {even : Bool} (a b : Letters n even) : Round n :=
  match a.val, b.val with
  | some a, some b => midpoint a b
  | some a, none => a
  | none, some b => b
  | none, none => 0

theorem edgeRound_symm {n : ℕ} {even : Bool} (a b : Letters n even) :
    edgeRound a b = edgeRound b a := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a <;> cases b <;> simp [edgeRound, midpoint, add_comm]

theorem edgeRound_unique {n : ℕ} {even : Bool} {a b c : Letters n even}
    (hb : a ≠ b) (hc : a ≠ c) (h : edgeRound a b = edgeRound a c) : b = c := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb'⟩
  rcases c with ⟨c, hc'⟩
  cases a with
  | none =>
    cases b <;> cases c <;> simp_all [edgeRound]
  | some a =>
    cases b with
    | none =>
      cases c with
      | none => rfl
      | some c =>
        change a = midpoint a c at h
        have h' := congrArg ((2 : Round n) * ·) h
        change (2 : Round n) * a = 2 * midpoint a c at h'
        rw [double_midpoint] at h'
        have he : a + a = a + c := (two_mul a).symm.trans h'
        exact (hc (Subtype.ext (congrArg some (add_left_cancel he)))).elim
    | some b =>
      cases c with
      | none =>
        change midpoint a b = a at h
        have h' := congrArg ((2 : Round n) * ·) h
        change (2 : Round n) * midpoint a b = 2 * a at h'
        rw [double_midpoint] at h'
        have he : a + b = a + a := h'.trans (two_mul a)
        exact (hb (Subtype.ext (congrArg some (add_left_cancel he).symm))).elim
      | some c =>
        change midpoint a b = midpoint a c at h
        have h' := congrArg ((2 : Round n) * ·) h
        change (2 : Round n) * midpoint a b = 2 * midpoint a c at h'
        rw [double_midpoint, double_midpoint] at h'
        exact Subtype.ext (congrArg some (add_left_cancel h'))

private def rotate {n : ℕ} {even : Bool} (c : Round n) (a : Letters n even) :
    Letters n even :=
  ⟨a.val.map (· + c), by rcases a with ⟨a, ha⟩; cases a <;> simpa using ha⟩

private theorem rotate_inv {n : ℕ} {even : Bool} (c : Round n) (a : Letters n even) :
    rotate (-c) (rotate c a) = a := by
  apply Subtype.ext
  rcases a with ⟨a, ha⟩
  cases a <;> simp [rotate]

private theorem rotate_injective {n : ℕ} {even : Bool} (c : Round n) :
    Function.Injective (@rotate n even c) := fun a b h =>
  (rotate_inv c a).symm.trans ((congrArg (rotate (-c)) h).trans (rotate_inv c b))

private theorem rotate_round {n : ℕ} {even : Bool} (c : Round n) {a b : Letters n even}
    (hne : a ≠ b) : edgeRound (rotate c a) (rotate c b) = edgeRound a b + c := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a with
  | none => cases b <;> simp_all [rotate, edgeRound]
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      change midpoint (a+c) (b+c) = midpoint a b + c
      have h := twice_half n
      unfold midpoint
      linear_combination c * h

private abbrev OrderedEdge (n : ℕ) (even : Bool) (j : Round n) :=
  {v : Letters n even × Letters n even // v.1 ≠ v.2 ∧ edgeRound v.1 v.2 = j}

abbrev Edges (n : ℕ) (even : Bool) (j : Round n) :=
  {v : Letters n even × Letters n even //
    letterIndex v.1 < letterIndex v.2 ∧ edgeRound v.1 v.2 = j}

private def rotateEdges (n : ℕ) (even : Bool) (i j : Round n) :
    OrderedEdge n even i ≃ OrderedEdge n even j := by
  let c := j-i
  refine
    { toFun := fun v => ⟨(rotate c v.val.1, rotate c v.val.2),
        fun h => v.property.1 (rotate_injective c h), by
          rw [rotate_round c v.property.1, v.property.2]
          dsimp [c]
          ring⟩
      invFun := fun v => ⟨(rotate (-c) v.val.1, rotate (-c) v.val.2),
        fun h => v.property.1 (rotate_injective (-c) h), by
          rw [rotate_round (-c) v.property.1, v.property.2]
          dsimp [c]
          ring⟩
      left_inv := fun v => Subtype.ext (Prod.ext (rotate_inv c _) (rotate_inv c _))
      right_inv := fun v => Subtype.ext (Prod.ext (by simpa using rotate_inv (-c) v.val.1)
        (by simpa using rotate_inv (-c) v.val.2)) }

private def orientationEquiv (n : ℕ) (even : Bool) (j : Round n) :
    Edges n even j × Bool ≃ OrderedEdge n even j where
  toFun v := if v.2 then
      ⟨v.1.val, fun h => (Nat.ne_of_lt v.1.property.1) (congrArg letterIndex h), v.1.property.2⟩
    else ⟨v.1.val.swap, fun h => (Nat.ne_of_lt v.1.property.1) (congrArg letterIndex h.symm),
      (edgeRound_symm _ _).trans v.1.property.2⟩
  invFun v := if h : letterIndex v.val.1 < letterIndex v.val.2 then
      (⟨v.val, h, v.property.2⟩, true)
    else
      have hn : letterIndex v.val.1 ≠ letterIndex v.val.2 := fun he =>
        v.property.1 (letterIndex_injective he)
      (⟨v.val.swap, by exact lt_of_le_of_ne (Nat.le_of_not_gt h) (Ne.symm hn),
        (edgeRound_symm _ _).trans v.property.2⟩, false)
  left_inv := by
    rintro ⟨v, bv⟩
    cases bv
    · have hn := Nat.not_lt_of_ge v.property.1.le
      simp [hn]
    · simp [v.property.1]
  right_inv := by
    intro v
    dsimp only
    by_cases h : letterIndex v.val.1 < letterIndex v.val.2 <;> simp [h]

private theorem ordered_edge_count (n : ℕ) (even : Bool) (j : Round n) :
    Fintype.card (OrderedEdge n even j) = 2 * (n + if even then 1 else 0) := by
  classical
  let L := Letters n even
  let e : (Σ c : Round n, OrderedEdge n even c) ≃ {p : L × L // p.1 ≠ p.2} :=
    { toFun := fun v => ⟨v.2.val, v.2.property.1⟩
      invFun := fun v => ⟨edgeRound v.val.1 v.val.2, ⟨v.val, v.property, rfl⟩⟩
      left_inv := by
        rintro ⟨c, ⟨v, hv, hc⟩⟩
        subst c
        rfl
      right_inv := fun _ => rfl }
  let D := Fintype.card (OrderedEdge n even j)
  have htotal : (2*n+1)*D = Fintype.card {p : L × L // p.1 ≠ p.2} := by
    rw [← Fintype.card_congr e, Fintype.card_sigma]
    have hconst (c : Round n) : Fintype.card (OrderedEdge n even c) = D :=
      Fintype.card_congr (rotateEdges n even c j)
    simp [hconst, Finset.sum_const, ZMod.card]
  have hdiag : Fintype.card {p : L × L // p.1 = p.2} = Fintype.card L := by
    apply Fintype.card_congr
    exact
      { toFun := fun p => p.val.1
        invFun := fun a => ⟨(a, a), rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl p.property)
        right_inv := fun _ => rfl }
  have hle : Fintype.card {p : L × L // p.1 = p.2} ≤ Fintype.card (L × L) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hsum : Fintype.card {p : L × L // p.1 ≠ p.2} +
      Fintype.card {p : L × L // p.1 = p.2} = Fintype.card (L × L) := by
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel hle
  rw [← htotal, hdiag, Fintype.card_prod] at hsum
  change (2*n+1)*D + Fintype.card (Letters n even) =
    Fintype.card (Letters n even) * Fintype.card (Letters n even) at hsum
  rw [letters_card] at hsum
  change D = _
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2*n+1)
  apply Nat.add_right_cancel (m := 2*n+1 + if even then 1 else 0)
  rw [hsum]
  cases even <;> simp <;> ring

/-- Every round has exactly the size of a perfect or a near-perfect matching. -/
theorem edges_card (n : ℕ) (even : Bool) (j : Round n) :
    Fintype.card (Edges n even j) = n + if even then 1 else 0 := by
  have h := Fintype.card_congr (orientationEquiv n even j)
  rw [Fintype.card_prod, Fintype.card_bool, ordered_edge_count] at h
  omega

end Reconstruction.ColorAlphabet
