import J1R14QueryFibre

/-! The whole printed exceptional basis, including non-diagonal rows:
for each coordinate exactly the three families in MAIN lines 2241–2269,
with rows selected by the declared interval. This constructs the previous
BasisFile rather than postulating a separate row correspondence. -/
namespace J1R14Query
open scoped BigOperators

universe u v w c p
variable {I : Type u} {S : Type v} {X : Type w} {Copy : Type c} {Pin : Type p}
variable [Fintype I] [DecidableEq I] [Fintype S] [LinearOrder S]

abbrev LocalBasis (S : Type v) [LinearOrder S] :=
  S ⊕ ({ab : S×S // ab.1 < ab.2} × Bool)

def indicatorInt (a u : S×S) : ℤ := if u = a then 1 else 0

def localEntry (b : LocalBasis S) (u : S×S) : ℤ :=
  match b with
  | .inl a => indicatorInt (a,a) u
  | .inr (ab,sgn) => indicatorInt ab.val u +
      (if sgn then -1 else 1) * indicatorInt (ab.val.2,ab.val.1) u

def oddBasis (b : LocalBasis S) : Bool :=
  match b with
  | .inl _ => false
  | .inr (_,sgn) => sgn

def basisWeight (q : I → LocalBasis S) : ℕ :=
  (Finset.univ.filter fun i => oddBasis (q i)).card

abbrev Exceptional (I : Type u) (S : Type v) [Fintype I] [LinearOrder S]
    (interval : Finset ℕ) := {q : I → LocalBasis S // basisWeight q ∉ interval}

def basisEntry (q : I → LocalBasis S) (u : MainProbe.Cell I S) : ℤ :=
  ∏ i, localEntry (q i) (u.1 i,u.2 i)

omit [Fintype I] [DecidableEq I] [Fintype S] in
theorem localEntry_cases (b : LocalBasis S) (u : S×S) :
    localEntry b u = 0 ∨ localEntry b u = 1 ∨ localEntry b u = -1 := by
  cases b with
  | inl a =>
    by_cases h : u = (a,a)
    · simp [localEntry,indicatorInt,h]
    · simp [localEntry,indicatorInt,h]
  | inr ab =>
    rcases ab with ⟨ab,b⟩
    have hne : ab.val ≠ (ab.val.2,ab.val.1) :=
      fun e => (ne_of_lt ab.property) (congrArg Prod.fst e)
    by_cases h₁ : u = ab.val
    · simp [localEntry,indicatorInt,h₁,hne]
    · by_cases h₂ : u = (ab.val.2,ab.val.1)
      · cases b <;> norm_num [localEntry,indicatorInt,h₂,Ne.symm hne]
      · simp [localEntry,indicatorInt,h₁,h₂]

omit [DecidableEq I] [Fintype S] in
theorem basisEntry_cases (q : I → LocalBasis S) (u : MainProbe.Cell I S) :
    basisEntry q u = 0 ∨ basisEntry q u = 1 ∨ basisEntry q u = -1 := by
  classical
  unfold basisEntry
  generalize Finset.univ (α := I) = is
  induction is using Finset.induction_on with
  | empty => simp
  | @insert a is ha hi =>
    rw [Finset.prod_insert ha]
    rcases localEntry_cases (q a) (u.1 a,u.2 a) with h | h | h <;>
      rcases hi with h' | h' | h' <;> norm_num [h,h']

def diagonalWord (D : MainProbe.DiagonalLayout I S X Copy Pin)
    (p : Pin) : I → LocalBasis S := fun i => .inl ((D.slot p).1 i)

omit [DecidableEq I] [Fintype S] in
theorem diagonalWeight (D : MainProbe.DiagonalLayout I S X Copy Pin) (p : Pin) :
    basisWeight (diagonalWord D p) = 0 := by
  simp [basisWeight,diagonalWord,oddBasis]

omit [DecidableEq I] [Fintype S] in
theorem diagonalEntry (D : MainProbe.DiagonalLayout I S X Copy Pin) (p : Pin)
    (u : MainProbe.Cell I S) :
    basisEntry (diagonalWord D p) u = if u = D.slot p then 1 else 0 := by
  classical
  by_cases h : u = D.slot p
  · subst u
    have he (i : I) : (D.slot p).2 i = (D.slot p).1 i := (congrFun (D.diagonal p) i).symm
    simp [basisEntry,diagonalWord,localEntry,indicatorInt,he]
  · have hx : ∃ i : I, (u.1 i,u.2 i) ≠ ((D.slot p).1 i,(D.slot p).1 i) := by
      by_contra! hn
      apply h
      exact Prod.ext (funext fun i => congrArg Prod.fst (hn i))
        (funext fun i => (congrArg Prod.snd (hn i)).trans (congrFun (D.diagonal p) i))
    obtain ⟨i,hi⟩ := hx
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      simp [diagonalWord,localEntry,indicatorInt,hi])

def printedBasis (D : MainProbe.DiagonalLayout I S X Copy Pin) (interval : Finset ℕ)
    (hOutside : 0 ∉ interval) : BasisFile (Basis:=Exceptional I S interval) D where
  entry q := basisEntry q.val
  diagonalIndex p := ⟨diagonalWord D p, by simpa only [diagonalWeight] using hOutside⟩
  exactDiagonal := diagonalEntry D

omit [DecidableEq I] [Fintype S] in
theorem printedBasis_signed (D : MainProbe.DiagonalLayout I S X Copy Pin)
    (interval : Finset ℕ) (hOutside : 0 ∉ interval) (q : Exceptional I S interval)
    (u : MainProbe.Cell I S) :
    (printedBasis D interval hOutside).entry q u = 0 ∨
    (printedBasis D interval hOutside).entry q u = 1 ∨
    (printedBasis D interval hOutside).entry q u = -1 :=
  basisEntry_cases q.val u


/-- Source-sized range for the genuine copied exceptional row, even when
several occupied cells take the same old-variable value. -/
theorem printed_read_bounds (D : MainProbe.DiagonalLayout I S X Copy Pin)
    (interval : Finset ℕ) (hOutside : 0 ∉ interval) (t : I) (g : S)
    (h : Copy × Exceptional I S interval) (x : X → Bool) :
    -(Fintype.card (MainProbe.Cell I S) : ℤ) ≤ rowRead D (printedBasis D interval hOutside) t g h x ∧
    rowRead D (printedBasis D interval hOutside) t g h x ≤
      (Fintype.card (MainProbe.Cell I S) : ℤ) := by
  let B := printedBasis D interval hOutside
  have he (u : MainProbe.Cell I S) :
      -1 ≤ B.entry h.2 u * (D.occupied h.1 u).elim 0 (groupBit D t g x) ∧
      B.entry h.2 u * (D.occupied h.1 u).elim 0 (groupBit D t g x) ≤ 1 := by
    cases ho : D.occupied h.1 u with
    | none => simp
    | some v =>
      have hB := printedBasis_signed D interval hOutside h.2 u
      change B.entry h.2 u = 0 ∨ B.entry h.2 u = 1 ∨ B.entry h.2 u = -1 at hB
      by_cases hm : D.variableWord v t = g ∧ x v = true
      · rcases hB with hB | hB | hB <;> norm_num [ho,groupBit,hm,hB]
      · simp [groupBit,hm]
  change -(Fintype.card (MainProbe.Cell I S) : ℤ) ≤ (∑ u, _) ∧
    (∑ u, _) ≤ (Fintype.card (MainProbe.Cell I S) : ℤ)
  constructor
  · calc
      -(Fintype.card (MainProbe.Cell I S) : ℤ) = ∑ _ : MainProbe.Cell I S, (-1:ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun u _ => (he u).1
  · calc
      _ ≤ ∑ _ : MainProbe.Cell I S, (1:ℤ) := Finset.sum_le_sum fun u _ => (he u).2
      _ = _ := by simp

#print axioms printed_read_bounds
#print axioms localEntry_cases
#print axioms basisEntry_cases
#print axioms diagonalWeight
#print axioms diagonalEntry
#print axioms printedBasis
#print axioms printedBasis_signed
end J1R14Query
