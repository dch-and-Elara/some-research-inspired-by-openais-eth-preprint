import AffineCostBits
import AffineCostExpr

/-!
The metered compiler uses Boolean cells, list and tree constructors, and
unary indices. An index has at most q successors. Pattern matching and
adding or removing one unary successor have constant charge. Proofs and the
step counter are annotations, as in AffineCost.Bit.Run.
-/

namespace AffineCompile

open AffineCost (Expr)
open AffineCost.Bit (Run)

def emit {A : Type} (a : A) : Run A := ⟨a, 8⟩

def mapList {A B : Type} (f : A → Run B) : List A → Run (List B)
  | [] => emit []
  | a :: as =>
    let x := f a
    let xs := mapList f as
    ⟨x.value :: xs.value, 16+x.steps+xs.steps⟩

@[simp] theorem mapList_value {A B : Type} (f : A → Run B) (xs : List A) :
    (mapList f xs).value = xs.map (fun x => (f x).value) := by
  induction xs <;> simp [mapList, emit, *]

theorem mapList_steps {A B : Type} (f : A → Run B) (xs : List A) (C : ℕ)
    (hc : ∀ a ∈ xs, (f a).steps ≤ C) :
    (mapList f xs).steps ≤ 8+xs.length*(16+C) := by
  induction xs with
  | nil => simp [mapList, emit]
  | cons a as ih =>
    have ha := hc a (by simp)
    have ht := ih (fun x hx => hc x (by simp [hx]))
    simp only [mapList, List.length_cons, Nat.add_mul, one_mul]
    omega

def appendList {A : Type} : List A → List A → Run (List A)
  | [], ys => emit ys
  | x :: xs, ys =>
    let z := appendList xs ys
    ⟨x :: z.value, 16+z.steps⟩

@[simp] theorem appendList_value {A : Type} (xs ys : List A) :
    (appendList xs ys).value = xs ++ ys := by
  induction xs <;> simp [appendList, emit, *]

theorem appendList_steps {A : Type} (xs ys : List A) :
    (appendList xs ys).steps = 8+16*xs.length := by
  induction xs <;> simp [appendList, emit, *, Nat.mul_succ]; omega

/-- Lexicographic list product, with the inner list traversed once per outer item. -/
def productList {A B : Type} : List A → List B → Run (List (A × B))
  | [], _ => emit []
  | a :: as, bs =>
    let row := mapList (fun b => emit (a,b)) bs
    let rest := productList as bs
    let out := appendList row.value rest.value
    ⟨out.value, 16+row.steps+rest.steps+out.steps⟩

@[simp] theorem productList_value {A B : Type} (as : List A) (bs : List B) :
    (productList as bs).value = as.product bs := by
  induction as <;> simp [productList, List.product, emit, *]

theorem productList_steps {A B : Type} (as : List A) (bs : List B) :
    (productList as bs).steps ≤ 8+as.length*(32+40*bs.length) := by
  induction as with
  | nil => simp [productList, emit]
  | cons a as ih =>
    have hm := mapList_steps (fun b => emit (a,b)) bs 8 (fun _ _ => le_rfl)
    simp only [productList, appendList_steps, mapList_value, List.length_map, List.length_cons,
      Nat.add_mul, one_mul] at *
    omega

def filterList {A : Type} (f : A → Run Bool) : List A → Run (List A)
  | [] => emit []
  | a :: as =>
    let keep := f a
    let rest := filterList f as
    ⟨if keep.value then a :: rest.value else rest.value, 16+keep.steps+rest.steps⟩

@[simp] theorem filterList_value {A : Type} (f : A → Run Bool) (xs : List A) :
    (filterList f xs).value = xs.filter (fun x => (f x).value) := by
  induction xs <;> simp [filterList, emit, List.filter_cons, *]

theorem filterList_steps {A : Type} (f : A → Run Bool) (xs : List A) (C : ℕ)
    (hc : ∀ a ∈ xs, (f a).steps ≤ C) :
    (filterList f xs).steps ≤ 8+xs.length*(16+C) := by
  induction xs with
  | nil => simp [filterList, emit]
  | cons a as ih =>
    have ha := hc a (by simp)
    have ht := ih (fun x hx => hc x (by simp [hx]))
    simp only [filterList, List.length_cons, Nat.add_mul, one_mul]
    omega

def allList {A : Type} (f : A → Run Bool) : List A → Run Bool
  | [] => emit true
  | a :: as =>
    let b := f a
    let c := allList f as
    ⟨b.value && c.value, 16+b.steps+c.steps⟩

@[simp] theorem allList_value {A : Type} (f : A → Run Bool) (xs : List A) :
    (allList f xs).value = xs.all (fun x => (f x).value) := by
  induction xs <;> simp [allList, emit, *]

theorem allList_steps {A : Type} (f : A → Run Bool) (xs : List A) (C : ℕ)
    (hc : ∀ a ∈ xs, (f a).steps ≤ C) :
    (allList f xs).steps ≤ 8+xs.length*(16+C) := by
  induction xs with
  | nil => simp [allList, emit]
  | cons a as ih =>
    have ha := hc a (by simp)
    have ht := ih (fun x hx => hc x (by simp [hx]))
    simp only [allList, List.length_cons, Nat.add_mul, one_mul]
    omega

def indexList : (q : ℕ) → Run (List (Fin q))
  | 0 => emit []
  | q+1 =>
    let xs := indexList q
    let ys := mapList (fun t => emit t.succ) xs.value
    ⟨0 :: ys.value, 16+xs.steps+ys.steps⟩

@[simp] theorem indexList_value (q : ℕ) : (indexList q).value = List.finRange q := by
  induction q with
  | zero => simp [indexList, emit]
  | succ q ih => simp [indexList, ih, emit, List.finRange_succ]

theorem indexList_steps (q : ℕ) : (indexList q).steps ≤ 32*(q+1)^2 := by
  induction q with
  | zero => decide
  | succ q ih =>
    have hm := mapList_steps (fun (t : Fin q) => emit t.succ) (indexList q).value 8
      (fun _ _ => le_rfl)
    simp only [indexList_value, List.length_finRange] at hm
    simp only [indexList]
    rw [indexList_value]
    nlinarith only [ih, hm]

abbrev Cells := List Bool

def readCell : Cells → ℕ → Run Bool
  | [], _ => emit false
  | b :: _, 0 => emit b
  | _ :: bs, n+1 =>
    let r := readCell bs n
    ⟨r.value, 16+r.steps⟩

@[simp] theorem readCell_value (xs : Cells) (n : ℕ) :
    (readCell xs n).value = (xs[n]?).getD false := by
  induction xs generalizing n with
  | nil => simp [readCell, emit]
  | cons x xs ih => cases n <;> simp [readCell, emit, ih]

theorem readCell_steps (xs : Cells) (n : ℕ) : (readCell xs n).steps ≤ 16*(n+1) := by
  induction xs generalizing n with
  | nil => simp [readCell, emit]; omega
  | cons x xs ih =>
    cases n with
    | zero => simp [readCell, emit]
    | succ n => have := ih n; simp only [readCell]; omega

def indexEq : ℕ → ℕ → Run Bool
  | 0, 0 => emit true
  | 0, _+1 | _+1, 0 => emit false
  | n+1, m+1 =>
    let r := indexEq n m
    ⟨r.value, 16+r.steps⟩

@[simp] theorem indexEq_value (n m : ℕ) : (indexEq n m).value = (n == m) := by
  induction n generalizing m <;> cases m <;> simp [indexEq, emit, *]

theorem indexEq_steps (n m : ℕ) : (indexEq n m).steps ≤ 16*(n+1) := by
  induction n generalizing m with
  | zero => cases m <;> simp [indexEq, emit]
  | succ n ih =>
    cases m with
    | zero => simp [indexEq, emit]; omega
    | succ m =>
      have hm := ih m
      simp only [indexEq]
      omega

def indexLt : ℕ → ℕ → Run Bool
  | _, 0 => emit false
  | 0, _+1 => emit true
  | n+1, m+1 =>
    let r := indexLt n m
    ⟨r.value, 16+r.steps⟩

@[simp] theorem indexLt_value (n m : ℕ) : (indexLt n m).value = decide (n < m) := by
  induction n generalizing m <;> cases m <;> simp [indexLt, emit, *]

theorem indexLt_steps (n m : ℕ) : (indexLt n m).steps ≤ 16*(n+1) := by
  induction n generalizing m with
  | zero => cases m <;> simp [indexLt, emit]
  | succ n ih =>
    cases m with
    | zero => simp [indexLt, emit]; omega
    | succ m =>
      have hm := ih m
      simp only [indexLt]
      omega

/-- Quotient and parity by stripping two unary successor cells at a time. -/
def indexHalf : ℕ → Run (ℕ × Bool)
  | 0 => emit (0,false)
  | 1 => emit (0,true)
  | n+2 =>
    let r := indexHalf n
    ⟨(r.value.1+1, r.value.2), 16+r.steps⟩

@[simp] theorem indexHalf_value : ∀ n : ℕ,
    (indexHalf n).value = (n/2, decide (n%2=1))
  | 0 => rfl
  | 1 => rfl
  | n+2 => by
    simp only [indexHalf, indexHalf_value n]
    congr 1
    · omega
    · by_cases h : n%2 = 1
      · have h' : (n+2)%2 = 1 := by omega
        simp [h,h']
      · have h' : (n+2)%2 ≠ 1 := by omega
        simp [h,h']

theorem indexHalf_steps : ∀ n : ℕ, (indexHalf n).steps ≤ 16*(n+1)
  | 0 => by decide
  | 1 => by decide
  | n+2 => by
    have := indexHalf_steps n
    simp only [indexHalf]
    omega

end AffineCompile
