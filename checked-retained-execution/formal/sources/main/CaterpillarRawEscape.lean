import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! A3 raw-table escape, derived from the explicit finite caterpillar graph.
Vertices of each kind have positions 0,...,k; 0 is the terminal end (reverse
of the paper's traversal order). The independent-set condition directly tests
edges of the graph, not a recursive count predicate. -/
namespace CaterpillarRawEscape

abbrev Word (k : ℕ) := Fin k → Bool
abbrev Bits (k : ℕ) := Word (k+1) × Word (k+1)

def consBit {k : ℕ} (b : Bool) (x : Word k) : Word (k+1) := Fin.cases b x
def tailBit {k : ℕ} (x : Word (k+1)) : Word k := fun i => x i.succ

@[simp] theorem consBit_zero {k : ℕ} (b : Bool) (x : Word k) : consBit b x 0 = b := rfl
@[simp] theorem consBit_succ {k : ℕ} (b : Bool) (x : Word k) (i : Fin k) :
    consBit b x i.succ = x i := by simp [consBit]
@[simp] theorem tailBit_cons {k : ℕ} (b : Bool) (x : Word k) :
    tailBit (consBit b x) = x := by funext i; simp [tailBit]
@[simp] theorem consBit_tail {k : ℕ} (x : Word (k+1)) :
    consBit (x 0) (tailBit x) = x := by
  funext i
  exact Fin.cases (by simp) (fun j => by simp [tailBit]) i

/-- The leftmost leaf is always enabled; the others are the raw switch word. -/
def enabledLeaf : (k : ℕ) → Word k → Word (k+1)
  | 0, _ => fun _ => true
  | k+1, w => consBit (w 0) (enabledLeaf k (tailBit w))

/-- On an actual spine edge i -> i+1, two spine vertices cannot both be chosen. -/
def spineLegal {k : ℕ} (spine : Word (k+1)) : Prop :=
  ∀ i j, i.val + 1 = j.val → spine i = true → spine j = false

/-- At each actual pendant edge, both endpoints cannot be chosen, and its
leaf is selectable only when enabled. -/
def leafLegal {k : ℕ} (available spine leaves : Word (k+1)) : Prop :=
  ∀ i, (spine i = true → leaves i = false) ∧ (leaves i = true → available i = true)

def valid (k : ℕ) (w : Word k) (p : Bits k) : Prop :=
  spineLegal p.1 ∧ leafLegal (enabledLeaf k w) p.1 p.2

theorem spineLegal_cons {k : ℕ} (head : Bool) (spine : Word (k+1)) :
    spineLegal (consBit head spine) ↔
      (head = true → spine 0 = false) ∧ spineLegal spine := by
  constructor
  · intro h
    constructor
    · intro hh
      have he := h 0 (0 : Fin (k+1)).succ (by simp) (by simpa using hh)
      simpa using he
    · intro i j hij hi
      have hh : i.succ.val + 1 = j.succ.val := by simp only [Fin.val_succ]; omega
      simpa using h i.succ j.succ hh (by simpa using hi)
  · rintro ⟨hhead,htail⟩ i j hij hsel
    revert hij hsel
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp
      · intro hj hs
        have he : j' = 0 := Fin.ext (by simp only [Fin.val_zero,Fin.val_succ] at hj ⊢; omega)
        subst j'
        simpa using hhead (by simpa using hs)
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro hj _
        simp only [Fin.val_zero,Fin.val_succ] at hj
        omega
      · intro hj hs
        have he : i'.val+1=j'.val := by simp only [Fin.val_succ] at hj; omega
        simpa using htail i' j' he (by simpa using hs)

theorem leafLegal_cons {k : ℕ} (avail head leaf : Bool) (a s l : Word (k+1)) :
    leafLegal (consBit avail a) (consBit head s) (consBit leaf l) ↔
      (head = true → leaf = false) ∧ (leaf = true → avail = true) ∧ leafLegal a s l := by
  simp only [leafLegal,Fin.forall_fin_succ,consBit_zero,consBit_succ]
  tauto

/-- Segmenting the actual edge constraints removes exactly one spine edge
and the head pendant edge. -/
theorem valid_cons {k : ℕ} (w : Word (k+1)) (head leaf : Bool) (p : Bits k) :
    valid (k+1) w (consBit head p.1,consBit leaf p.2) ↔
      (head = true → p.1 0 = false) ∧ (head = true → leaf = false) ∧
      (leaf = true → w 0 = true) ∧ valid k (tailBit w) p := by
  simp only [valid,enabledLeaf,spineLegal_cons,leafLegal_cons]
  tauto

theorem valid_head_tail {k : ℕ} (w : Word (k+1)) (p : Bits (k+1)) :
    valid (k+1) w p ↔
      (p.1 0 = true → p.1 (0 : Fin (k+1)).succ = false) ∧
      (p.1 0 = true → p.2 0 = false) ∧ (p.2 0 = true → w 0 = true) ∧
      valid k (tailBit w) (tailBit p.1,tailBit p.2) := by
  simpa only [consBit_tail,tailBit] using valid_cons w (p.1 0) (p.2 0)
    (tailBit p.1,tailBit p.2)

abbrev Choices (k : ℕ) (w : Word k) (endBit : Bool) :=
  {p : Bits k // valid k w p ∧ p.1 0 = endBit}

noncomputable instance choicesFintype (k : ℕ) (w : Word k) (b : Bool) :
    Fintype (Choices k w b) := Fintype.ofFinite _

abbrev LeafChoices (s : Bool) := {b : Bool // b = true → s = true}

theorem leafChoices_card (s : Bool) : Fintype.card (LeafChoices s) = if s then 2 else 1 := by
  cases s <;> decide

private theorem finOne_eq (i : Fin (0+1)) : i = 0 :=
  by apply Fin.ext; change i.val = 0; have h := i.isLt; omega

theorem valid_zero (w : Word 0) (p : Bits 0) :
    valid 0 w p ↔ (p.1 0 = true → p.2 0 = false) := by
  constructor
  · intro h; exact (h.2 0).1
  · intro h
    constructor
    · intro i j he _
      have hi : i = 0 := finOne_eq i
      have hj : j = 0 := finOne_eq j
      subst i
      subst j
      simp at he
    · intro i
      have hi : i = 0 := finOne_eq i
      subst i
      exact ⟨h,fun _ => rfl⟩

def baseAbsent (w : Word 0) : Choices 0 w false ≃ Bool where
  toFun p := p.1.2 0
  invFun b := ⟨(fun _ => false,fun _ => b), (valid_zero w _).mpr (by simp), rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> funext i <;> have hi : i = 0 := finOne_eq i <;> subst i
    · exact p.2.2.symm
    · rfl
  right_inv _ := rfl

def basePresent (w : Word 0) : Choices 0 w true ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(fun _ => true,fun _ => false), (valid_zero w _).mpr (by simp), rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> funext i <;> have hi : i = 0 := finOne_eq i <;> subst i
    · exact p.2.2.symm
    · exact ((valid_zero w p.val).mp p.2.1 p.2.2).symm
  right_inv _ := rfl

/-- Explicit decomposition of all legal actual graph assignments when the
terminal spine vertex is absent. -/
def extendAbsent (k : ℕ) (w : Word (k+1)) : Choices (k+1) w false ≃
    LeafChoices (w 0) × (Σ b : Bool, Choices k (tailBit w) b) where
  toFun p := by
    have h := (valid_head_tail w p.val).mp p.2.1
    exact (⟨p.1.2 0,h.2.2.1⟩,
      ⟨tailBit p.1.1 0,⟨(tailBit p.1.1,tailBit p.1.2),h.2.2.2,rfl⟩⟩)
  invFun q := by
    rcases q with ⟨l,⟨_,x⟩⟩
    refine ⟨(consBit false x.1.1,consBit l.val x.1.2),?_,by simp⟩
    exact (valid_cons w false l.val x.val).mpr
      ⟨by simp,by simp,l.property,x.2.1⟩
  left_inv p := by
    apply Subtype.ext
    change (consBit false (tailBit p.1.1),consBit (p.1.2 0) (tailBit p.1.2)) = p.val
    apply Prod.ext
    · exact (congrArg (fun b => consBit b (tailBit p.1.1)) p.2.2.symm).trans
        (consBit_tail p.1.1)
    · exact consBit_tail p.1.2
  right_inv q := by
    rcases q with ⟨⟨l,hl⟩,⟨b,⟨⟨x,y⟩,hv,hb⟩⟩⟩
    change x 0 = b at hb
    subst b
    simp [tailBit_cons]

/-- With terminal present, both of its neighbors are forced absent. -/
def extendPresent (k : ℕ) (w : Word (k+1)) :
    Choices (k+1) w true ≃ Choices k (tailBit w) false where
  toFun p := by
    have h := (valid_head_tail w p.val).mp p.2.1
    exact ⟨(tailBit p.1.1,tailBit p.1.2),h.2.2.2,h.1 p.2.2⟩
  invFun q := by
    refine ⟨(consBit true q.1.1,consBit false q.1.2),?_,by simp⟩
    exact (valid_cons w true false q.val).mpr ⟨fun _ => q.2.2,by simp,by simp,q.2.1⟩
  left_inv p := by
    have h := (valid_head_tail w p.val).mp p.2.1
    apply Subtype.ext
    change (consBit true (tailBit p.1.1),consBit false (tailBit p.1.2)) = p.val
    apply Prod.ext
    · exact (congrArg (fun b => consBit b (tailBit p.1.1)) p.2.2.symm).trans
        (consBit_tail p.1.1)
    · exact (congrArg (fun b => consBit b (tailBit p.1.2)) (h.2.1 p.2.2).symm).trans
        (consBit_tail p.1.2)
  right_inv q := by
    apply Subtype.ext
    rcases q with ⟨⟨x,y⟩,h⟩
    change (tailBit (consBit true x),tailBit (consBit false y)) = (x,y)
    simp

#print axioms valid_cons
#print axioms extendAbsent
#print axioms extendPresent


/-- A pair carries counts (last spine absent, last spine present). -/
def step (s : Bool) (p : ℕ × ℕ) : ℕ × ℕ :=
  ((if s then 2 else 1) * (p.1+p.2),p.1)

def run : (k : ℕ) → Word k → ℕ × ℕ
  | 0, _ => (2,1)
  | k+1, w => step (w 0) (run k (tailBit w))

/-- End-to-end verification from the actual adjacency relation, with no
assumed path transfer matrix. -/
theorem actual_card_run (k : ℕ) (w : Word k) :
    (Fintype.card (Choices k w false),Fintype.card (Choices k w true)) = run k w := by
  induction k with
  | zero =>
    apply Prod.ext
    · exact (Fintype.card_congr (baseAbsent w)).trans Fintype.card_bool
    · exact (Fintype.card_congr (basePresent w)).trans Fintype.card_unit
  | succ k ih =>
    have ha := congrArg Prod.fst (ih (tailBit w))
    have hb := congrArg Prod.snd (ih (tailBit w))
    apply Prod.ext
    · change Fintype.card (Choices (k+1) w false) =
        (if w 0 then 2 else 1) * ((run k (tailBit w)).1+(run k (tailBit w)).2)
      rw [Fintype.card_congr (extendAbsent k w), Fintype.card_prod,leafChoices_card,
        Fintype.card_sigma,Fintype.sum_bool]
      change (if w 0 then 2 else 1) *
        (Fintype.card (Choices k (tailBit w) true) + Fintype.card (Choices k (tailBit w) false)) = _
      rw [show Fintype.card (Choices k (tailBit w) false) = (run k (tailBit w)).1 from ha,
        show Fintype.card (Choices k (tailBit w) true) = (run k (tailBit w)).2 from hb,add_comm ((run k (tailBit w)).2)]
    · exact (Fintype.card_congr (extendPresent k w)).trans ha

abbrev TerminalChoices (k : ℕ) (w : Word k) (b : Bool) :=
  {p : Bits k // valid k w p ∧ (p.1 0 = false ∨ b = true)}

noncomputable instance terminalFintype (k : ℕ) (w : Word k) (b : Bool) :
    Fintype (TerminalChoices k w b) := Fintype.ofFinite _

def terminalOff (k : ℕ) (w : Word k) : TerminalChoices k w false ≃ Choices k w false where
  toFun p := ⟨p.val,p.2.1,p.2.2.resolve_right Bool.false_ne_true⟩
  invFun p := ⟨p.val,p.2.1,Or.inl p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def terminalOn (k : ℕ) (w : Word k) : TerminalChoices k w true ≃ (Σ b : Bool, Choices k w b) where
  toFun p := ⟨p.1.1 0,⟨p.val,p.2.1,rfl⟩⟩
  invFun p := ⟨p.2.val,p.2.2.1,Or.inr rfl⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨b,⟨p,h,hb⟩⟩
    subst b
    rfl

/-- Pair of values satisfying the detached, actual clause b OR c. -/
abbrev Detached := {p : Bool × Bool // (p.1 || p.2) = true}

theorem detached_card : Fintype.card Detached = 3 := by decide

def answer (k : ℕ) (w : Word k) (b : Bool) : ℕ :=
  if b then 3*((run k w).1+(run k w).2) else 3*(run k w).1

/-- Exact counts with the two possible physical terminal settings. -/
theorem actual_answer (k : ℕ) (w : Word k) (b : Bool) :
    Fintype.card (Detached × TerminalChoices k w b) = answer k w b := by
  rw [Fintype.card_prod,detached_card]
  have ha : Fintype.card (Choices k w false) = (run k w).1 :=
    congrArg Prod.fst (actual_card_run k w)
  have hb : Fintype.card (Choices k w true) = (run k w).2 :=
    congrArg Prod.snd (actual_card_run k w)
  cases b
  · simp only [answer,Bool.false_eq_true,ite_false,Fintype.card_congr (terminalOff k w),ha]
  · simp only [answer,ite_true,Fintype.card_congr (terminalOn k w),
      Fintype.card_sigma,Fintype.sum_bool,ha,hb,add_comm ((run k w).2)]

/-- Raw uncontracted binary switch clause ¬x OR L_s(y). -/
def table (s x y : Bool) : Bool := (!x) || (if s then y else !y)

/-- One fixed legal original table address directly reads the input bit. -/
@[simp] theorem table_read (s : Bool) : table s true true = s := by cases s <;> decide

/-- When equality sets the ports to one common value, this same switch
table enforces that a marked vertex must be enabled. -/
theorem table_joined (s x : Bool) : table s x x = ((!x) || s) := by
  cases s <;> cases x <;> decide

/-- One fixed address for every variable leaf switch and the terminal. -/
abbrev RawAddress (k : ℕ) := Fin k ⊕ Unit

theorem rawAddress_count (k : ℕ) : Fintype.card (RawAddress k) = k+1 := by
  simp [RawAddress]

def read (k : ℕ) (w : Word k) (b : Bool) : RawAddress k → Bool
  | Sum.inl i => table (w i) true true
  | Sum.inr _ => table b true true

def rawDecoder (k : ℕ) (acquired : RawAddress k → Bool) : ℕ :=
  answer k (fun i => acquired (Sum.inl i)) (acquired (Sum.inr ()))

theorem rawDecoder_correct (k : ℕ) (w : Word k) (b : Bool) :
    rawDecoder k (read k w b) = Fintype.card (Detached × TerminalChoices k w b) := by
  rw [actual_answer]
  simp [rawDecoder,read]

theorem step_total_bound (s : Bool) (p : ℕ × ℕ) :
    (step s p).1+(step s p).2 ≤ 3*(p.1+p.2) := by
  cases s <;> simp [step] <;> omega

/-- At prefix length j even the total A+B is at most 3^(j+1). -/
theorem run_total_bound (k : ℕ) (w : Word k) :
    (run k w).1+(run k w).2 ≤ 3^(k+1) := by
  induction k with
  | zero => decide +revert
  | succ k ih =>
    calc
      _ ≤ 3*((run k (tailBit w)).1+(run k (tailBit w)).2) := step_total_bound _ _
      _ ≤ 3*3^(k+1) := Nat.mul_le_mul_left _ (ih _)
      _ = _ := by rw [pow_succ]; exact Nat.mul_comm _ _

theorem answer_bound (k : ℕ) (w : Word k) (b : Bool) :
    answer k w b ≤ 3^(k+2) := by
  have h := Nat.mul_le_mul_left 3 (run_total_bound k w)
  have hpow : 3*3^(k+1) = 3^(k+2) := Nat.pow_succ'.symm
  rw [hpow] at h
  cases b <;> simp only [answer,ite_true,ite_false,Bool.false_eq_true] <;> omega

theorem run_total_bits (k : ℕ) (w : Word k) :
    Nat.size ((run k w).1+(run k w).2) ≤ 2*(k+1) := by
  apply Nat.size_le.mpr
  rw [pow_mul]
  have hlt : (3:ℕ)^(k+1) < 4^(k+1) :=
    Nat.pow_lt_pow_left (by decide : (3:ℕ) < 4) (by omega : k+1 ≠ 0)
  exact (run_total_bound k w).trans_lt hlt

theorem run_coordinate_bits (k : ℕ) (w : Word k) :
    Nat.size (run k w).1 ≤ 2*(k+1) ∧ Nat.size (run k w).2 ≤ 2*(k+1) := by
  constructor
  · exact (Nat.size_le_size (Nat.le_add_right _ _)).trans (run_total_bits k w)
  · exact (Nat.size_le_size (Nat.le_add_left _ _)).trans (run_total_bits k w)

/-- Actual answer bits, including the detached multiplier, are ≤2k+4. -/
theorem answer_bits (k : ℕ) (w : Word k) (b : Bool) : Nat.size (answer k w b) ≤ 2*(k+2) := by
  apply Nat.size_le.mpr
  rw [pow_mul]
  have hlt : (3:ℕ)^(k+2) < 4^(k+2) :=
    Nat.pow_lt_pow_left (by decide : (3:ℕ) < 4) (by omega : k+2 ≠ 0)
  exact (answer_bound k w b).trans_lt hlt

#print axioms actual_card_run
#print axioms actual_answer
#print axioms table_read
#print axioms table_joined
#print axioms rawAddress_count
#print axioms rawDecoder_correct
#print axioms run_total_bound
#print axioms run_coordinate_bits
#print axioms answer_bits


/-- The physical five-copy directed implication cycle permits precisely one
common bit. This proof is independent of which two distinct copies the
switch clause uses for its raw table ports. -/
theorem implication_cycle5_constant (b : Fin 5 → Bool)
    (h : ∀ i, b i = true → b (i+1) = true) : ∀ i, b i = b 0 := by
  have h01 : b 0 = true → b 1 = true := h 0
  have h12 : b 1 = true → b 2 = true := h 1
  have h23 : b 2 = true → b 3 = true := h 2
  have h34 : b 3 = true → b 4 = true := h 3
  have h40 : b 4 = true → b 0 = true := h 4
  have hw : ∀ i, b i = true ↔ b 0 = true := by
    intro i
    fin_cases i
    · exact Iff.rfl
    · exact ⟨h40 ∘ h34 ∘ h23 ∘ h12,h01⟩
    · exact ⟨h40 ∘ h34 ∘ h23,h12 ∘ h01⟩
    · exact ⟨h40 ∘ h34,h23 ∘ h12 ∘ h01⟩
    · exact ⟨h40,h34 ∘ h23 ∘ h12 ∘ h01⟩
  intro i
  have hi := hw i
  cases hb : b i <;> cases h0 : b 0 <;> simp_all

/-- Cycle and availability-clause semantics reduce without invoking any
interpolation: either all old copies are zero, or the switch is on and
all old copies are one. -/
theorem joined_switch_constraint (b : Fin 5 → Bool) (s : Bool) (i j : Fin 5)
    (h : ∀ q, b q = true → b (q+1) = true) :
    table s (b i) (b j) = true ↔ (b 0 = true → s = true) := by
  rw [implication_cycle5_constant b h i,implication_cycle5_constant b h j,table_joined]
  cases s <;> cases hb : b 0 <;> simp

#print axioms implication_cycle5_constant
#print axioms joined_switch_constraint


/-- The conditional multiplication by 2 is a one-bit shift, not a general product. -/
theorem step_uses_add_shift (s : Bool) (p : ℕ × ℕ) :
    step s p = (if s then (p.1+p.2) <<< 1 else p.1+p.2,p.1) := by
  cases s <;> simp [step,Nat.shiftLeft_eq,mul_comm]

/-- Sum of operand widths for the one addition per step. This prices the
arithmetic recurrence structurally; it is not a machine timing model. -/
def additionWidths : (k : ℕ) → Word k → ℕ
  | 0, _ => 0
  | k+1, w => additionWidths k (tailBit w) +
      max (Nat.size (run k (tailBit w)).1) (Nat.size (run k (tailBit w)).2)

theorem quadratic_addition_widths (k : ℕ) (w : Word k) :
    additionWidths k w ≤ k*(k+1) := by
  induction k with
  | zero => decide +revert
  | succ k ih =>
    obtain ⟨ha,hb⟩ := run_coordinate_bits k (tailBit w)
    have hmax := max_le ha hb
    calc
      _ ≤ k*(k+1)+2*(k+1) := Nat.add_le_add (ih (tailBit w)) hmax
      _ = _ := by ring

#print axioms step_uses_add_shift
#print axioms quadratic_addition_widths

end CaterpillarRawEscape
