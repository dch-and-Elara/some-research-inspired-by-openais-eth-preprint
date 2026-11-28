import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Endpoint counts for the caterpillar in (C5), their attained output range,
and the bit budget of an arbitrary decoder. Boolean vertex markings encode
the caterpillar itself, with explicit leaf availability and edge constraints.
Index zero in a word is the last leaf processed. The cubic graph embedding,
the five-copy CNF identification and the native slot encoding are paper steps. -/

set_option autoImplicit false
set_option warningAsError true

namespace CaterpillarRange

abbrev Word (k : ℕ) := Fin k → Bool

/-- The endpoint-absent and endpoint-present independent-set counts. -/
def step (s : Bool) (p : ℕ × ℕ) : ℕ × ℕ :=
  ((if s then 2 else 1) * (p.1 + p.2), p.1)

def counts : (k : ℕ) → Word k → ℕ × ℕ
  | 0, _ => (2, 1)
  | k + 1, w => step (w 0) (counts k (fun i => w i.succ))

theorem counts_order (k : ℕ) (w : Word k) :
    0 < (counts k w).2 ∧ (counts k w).2 < (counts k w).1 := by
  induction k with
  | zero => decide +revert
  | succ k ih =>
    obtain ⟨hpos, hlt⟩ := ih (fun i => w i.succ)
    cases hs : w 0 <;> simp [counts, step, hs] <;> omega

def ratio (p : ℕ × ℕ) : ℚ := (p.1 : ℚ) / (p.2 : ℚ)

def update (s : Bool) (x : ℚ) : ℚ := (if s then 2 else 1) * (1 + x⁻¹)

theorem ratio_gt_one (k : ℕ) (w : Word k) : 1 < ratio (counts k w) := by
  obtain ⟨hpos, hlt⟩ := counts_order k w
  have hpos' : (0 : ℚ) < (counts k w).2 := by exact_mod_cast hpos
  apply (lt_div_iff₀ hpos').2
  simpa only [one_mul] using (show ((counts k w).2 : ℚ) < (counts k w).1 by exact_mod_cast hlt)

theorem ratio_step (s : Bool) (p : ℕ × ℕ) (hB : 0 < p.2) (hA : p.2 < p.1) :
    ratio (step s p) = update s (ratio p) := by
  have ha : (p.1 : ℚ) ≠ 0 := by exact_mod_cast (hB.trans hA).ne'
  have hb : (p.2 : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  cases s <;> simp only [step, ratio, update, Bool.false_eq_true, ↓reduceIte,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, inv_div, one_mul]
    <;> field_simp

/-- The two rational branches have disjoint open ranges above one. -/
theorem update_ranges {x : ℚ} (hx : 1 < x) :
    (1 < update false x ∧ update false x < 2) ∧
      (2 < update true x ∧ update true x < 4) := by
  have hlo : 0 < x⁻¹ := inv_pos.mpr (zero_lt_one.trans hx)
  have hhi : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  simp only [update, Bool.false_eq_true, ↓reduceIte, one_mul]
  constructor <;> constructor <;> linarith

theorem update_injective {s t : Bool} {x y : ℚ} (hx : 1 < x) (hy : 1 < y)
    (h : update s x = update t y) : s = t ∧ x = y := by
  obtain ⟨⟨_, hxl⟩, hxr, _⟩ := update_ranges hx
  obtain ⟨⟨_, hyl⟩, hyr, _⟩ := update_ranges hy
  have hs : s = t := by
    cases s <;> cases t
    · rfl
    · exact False.elim ((hxl.trans hyr).ne h)
    · exact False.elim ((hyl.trans hxr).ne h.symm)
    · rfl
  subst t
  refine ⟨rfl, ?_⟩
  cases s <;> simp [update] at h <;> exact h

theorem ratio_injective (k : ℕ) : Function.Injective (fun w : Word k => ratio (counts k w)) := by
  induction k with
  | zero => intro x y _; exact Subsingleton.elim x y
  | succ k ih =>
    intro x y h
    let u : Word k := fun i => x i.succ
    let v : Word k := fun i => y i.succ
    change ratio (step (x 0) (counts k u)) = ratio (step (y 0) (counts k v)) at h
    rw [ratio_step _ _ (counts_order k u).1 (counts_order k u).2,
      ratio_step _ _ (counts_order k v).1 (counts_order k v).2] at h
    obtain ⟨hhead, hprev⟩ := update_injective (ratio_gt_one k u) (ratio_gt_one k v) h
    have htail := ih hprev
    funext i
    exact Fin.cases hhead (fun j => congrFun htail j) i

/-- Toggling the endpoint of the physical five-copy family gives one of two counts. -/
def output (k : ℕ) (x : Word k × Bool) : ℕ :=
  let p := counts k x.1
  if x.2 then 3 * (p.1 + p.2) else 3 * p.1

/-- With the final spine bit specified separately, a marking chooses the
final leaf, the preceding spine vertex, and all earlier vertices. At the
left end only its private leaf remains. Every leaf and spine bit occurs once. -/
def Marking : ℕ → Type
  | 0 => Bool
  | k + 1 => Bool × Bool × Marking k

instance markingFintype : (k : ℕ) → Fintype (Marking k)
  | 0 => inferInstanceAs (Fintype Bool)
  | k + 1 => by
    letI := markingFintype k
    exact inferInstanceAs (Fintype (Bool × Bool × Marking k))

/-- Test leaf availability and the two edges incident to the last spine
vertex in this prefix. The base leaf is always enabled. -/
def independent : (k : ℕ) → Word k → Bool → Marking k → Prop
  | 0, _, false, _ => True
  | 0, _, true, leaf => leaf = false
  | k + 1, w, false, (leaf, previous, rest) =>
      (leaf = false ∨ w 0 = true) ∧ independent k (fun i => w i.succ) previous rest
  | k + 1, w, true, (leaf, previous, rest) =>
      leaf = false ∧ previous = false ∧ independent k (fun i => w i.succ) previous rest

abbrev Selections (k : ℕ) (w : Word k) (endpoint : Bool) :=
  {p : Marking k // independent k w endpoint p}

noncomputable instance selectionsFintype (k : ℕ) (w : Word k) (endpoint : Bool) :
    Fintype (Selections k w endpoint) := Fintype.ofFinite _

abbrev LeafOptions (s : Bool) := {l : Bool // l = false ∨ s = true}

theorem leaf_options_card (s : Bool) : Fintype.card (LeafOptions s) = if s then 2 else 1 := by
  cases s <;> decide

private def baseAbsent (w : Word 0) : Selections 0 w false ≃ Bool where
  toFun p := p.val
  invFun t := ⟨t, trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def basePresent (w : Word 0) : Selections 0 w true ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨false, rfl⟩
  left_inv p := Subtype.ext p.property.symm
  right_inv _ := rfl

private def appendAbsent (k : ℕ) (w : Word (k+1)) :
    Selections (k+1) w false ≃
      LeafOptions (w 0) × (Σ b : Bool, Selections k (fun i => w i.succ) b) where
  toFun p := (⟨p.val.1, p.property.1⟩, ⟨p.val.2.1, ⟨p.val.2.2, p.property.2⟩⟩)
  invFun p := ⟨(p.1.val, p.2.1, p.2.2.val), p.1.property, p.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def appendPresent (k : ℕ) (w : Word (k+1)) :
    Selections (k+1) w true ≃ Selections k (fun i => w i.succ) false where
  toFun p := ⟨p.val.2.2, p.property.2.1 ▸ p.property.2.2⟩
  invFun p := ⟨(false, false, p.val), rfl, rfl, p.property⟩
  left_inv p := by
    rcases p with ⟨⟨l,b,r⟩,hl,hb,hr⟩
    subst l
    subst b
    rfl
  right_inv _ := rfl

/-- The integer recurrence counts all independent Boolean markings on the
explicit spine and leaves, for both endpoint states. -/
theorem selections_card (k : ℕ) (w : Word k) :
    (Fintype.card (Selections k w false), Fintype.card (Selections k w true)) = counts k w := by
  induction k with
  | zero =>
    apply Prod.ext
    · exact (Fintype.card_congr (baseAbsent w)).trans Fintype.card_bool
    · exact (Fintype.card_congr (basePresent w)).trans (by change Fintype.card Unit = 1; decide)
  | succ k ih =>
    let t : Word k := fun i => w i.succ
    have hp : Fintype.card (Selections k t false) = (counts k t).1 := congrArg Prod.fst (ih t)
    have hq : Fintype.card (Selections k t true) = (counts k t).2 := congrArg Prod.snd (ih t)
    apply Prod.ext
    · change Fintype.card (Selections (k+1) w false) = (if w 0 then 2 else 1) *
        ((counts k t).1 + (counts k t).2)
      rw [Fintype.card_congr (appendAbsent k w), Fintype.card_prod, leaf_options_card,
        Fintype.card_sigma, Fintype.sum_bool, hp, hq, Nat.add_comm (counts k t).2 (counts k t).1]
    · exact (Fintype.card_congr (appendPresent k w)).trans hp

/-- All possible selections after fixing the availability of the final spine. -/
def EnabledSelections (k : ℕ) (w : Word k) : Bool → Type
  | false => Selections k w false
  | true => Σ b : Bool, Selections k w b

noncomputable instance enabledFintype (k : ℕ) (w : Word k) :
    (b : Bool) → Fintype (EnabledSelections k w b)
  | false => selectionsFintype k w false
  | true => inferInstanceAs (Fintype (Σ b : Bool, Selections k w b))

theorem output_eq_selections (k : ℕ) (w : Word k) (b : Bool) :
    output k (w,b) = 3 * Fintype.card (EnabledSelections k w b) := by
  have hp : Fintype.card (Selections k w false) = (counts k w).1 := congrArg Prod.fst (selections_card k w)
  have hq : Fintype.card (Selections k w true) = (counts k w).2 := congrArg Prod.snd (selections_card k w)
  cases b
  · change 3 * (counts k w).1 = 3 * Fintype.card (Selections k w false)
    rw [hp]
  · change 3 * ((counts k w).1 + (counts k w).2) = 3 * Fintype.card (Σ b : Bool, Selections k w b)
    rw [Fintype.card_sigma, Fintype.sum_bool, hp, hq, Nat.add_comm (counts k w).2 (counts k w).1]

theorem output_pair_injective (k : ℕ) : Function.Injective
    (fun w : Word k => (output k (w, false), output k (w, true))) := by
  intro x y h
  have hoff := congrArg Prod.fst h
  have hon := congrArg Prod.snd h
  change 3 * (counts k x).1 = 3 * (counts k y).1 at hoff
  change 3 * ((counts k x).1 + (counts k x).2) = 3 * ((counts k y).1 + (counts k y).2) at hon
  apply ratio_injective k
  apply congrArg ratio
  apply Prod.ext <;> omega

def attained (k : ℕ) : Finset ℕ := Finset.univ.image (output k)

theorem mem_attained (k : ℕ) (x : Word k × Bool) : output k x ∈ attained k :=
  Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

/-- Both coordinates of every output pair are real outputs on the same fixed topology. -/
theorem output_range_square (k : ℕ) : 2 ^ k ≤ (attained k).card ^ 2 := by
  let f (w : Word k) : (attained k) × (attained k) :=
    (⟨_, mem_attained k (w, false)⟩, ⟨_, mem_attained k (w, true)⟩)
  have hf : Function.Injective f := by
    intro x y h
    apply output_pair_injective k
    exact congrArg (fun q : (attained k) × (attained k) => (q.1.val, q.2.val)) h
  simpa [Word, pow_two] using Fintype.card_le_of_injective f hf

/-- An arbitrary exact decoder on a finite transcript alphabet can attain at
most as many distinct answers as it has possible transcripts. -/
theorem range_le_transcripts {X T Y : Type*} [Fintype X] [Fintype T] [DecidableEq Y]
    (answer : X → Y) (message : X → T) (decode : T → Y)
    (h : ∀ x, decode (message x) = answer x) :
    (Finset.univ.image answer).card ≤ Fintype.card T := by
  have hsub : Finset.univ.image answer ⊆ Finset.univ.image decode := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨message x, Finset.mem_univ _, h x⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- B bits from the pooled menu and b additional input-dependent bits. -/
theorem exact_decoder_bit_budget (k B b : ℕ)
    (menu : Word k × Bool → Word B) (side : Word k × Bool → Word b)
    (decode : Word B × Word b → ℕ)
    (correct : ∀ x, decode (menu x, side x) = output k x) :
    k ≤ 2 * (B + b) := by
  have hcap : (attained k).card ≤ 2 ^ (B + b) := by
    simpa [attained, Word, pow_add] using
      range_le_transcripts (output k) (fun x => (menu x, side x)) decode correct
  have hsq := (output_range_square k).trans (Nat.pow_le_pow_left hcap 2)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [Nat.mul_comm 2 (B + b), pow_mul]
  exact hsq

#print axioms counts_order
#print axioms ratio_gt_one
#print axioms ratio_step
#print axioms update_ranges
#print axioms update_injective
#print axioms ratio_injective
#print axioms leaf_options_card
#print axioms selections_card
#print axioms output_eq_selections
#print axioms output_pair_injective
#print axioms mem_attained
#print axioms output_range_square
#print axioms range_le_transcripts
#print axioms exact_decoder_bit_budget

end CaterpillarRange
