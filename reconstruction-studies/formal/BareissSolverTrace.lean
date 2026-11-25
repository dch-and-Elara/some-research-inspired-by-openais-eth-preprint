import BareissSolver

namespace Reconstruction.BareissSolver

inductive ScalarOp where
  | testZero (a : ℤ)
  | mul (a b : ℤ)
  | add (a b : ℤ)
  | sub (a b : ℤ)
  | exactDiv (a b : ℤ)

def ScalarOp.operands : ScalarOp → List ℤ
  | .testZero a => [a]
  | .mul a b | .add a b | .sub a b | .exactDiv a b => [a,b]

def ScalarOp.Within (C : ℕ) (op : ScalarOp) : Prop :=
  ∀ z ∈ op.operands, z.natAbs ≤ C

def ScalarOp.DivisionExact : ScalarOp → Prop
  | .exactDiv a b => b ≠ 0 ∧ b ∣ a
  | _ => True

def zeroTrace {m n : ℕ} (M : IntegerAugment m n) : List ScalarOp :=
  (rhsScan M).tested.map fun i => .testZero (M i none)

def pivotTrace {m n : ℕ} (M : IntegerAugment m n) : List ScalarOp :=
  (pivotScan M).tested.map fun p => .testZero (M p.1 (some p.2))

def columns (n : ℕ) : List (Option (Fin n)) := none :: (List.finRange n).map some

def forwardCellTrace {m n : ℕ} (M : IntegerAugment (m+1) (n+1)) (d : ℤ)
    (i : Fin (m+1)) (j : Fin (n+1)) (u : Fin m) (v : Option (Fin n)) : List ScalarOp :=
  let p := M i (some j)
  let a := M (i.succAbove u) (v.map j.succAbove)
  let c := M (i.succAbove u) (some j)
  let r := M i (v.map j.succAbove)
  [.mul p a, .mul c r, .sub (p*a) (c*r), .exactDiv (forwardDividend M i j u v) d]

def forwardTrace {m n : ℕ} (M : IntegerAugment (m+1) (n+1)) (d : ℤ)
    (i : Fin (m+1)) (j : Fin (n+1)) : List ScalarOp :=
  (List.finRange m).flatMap fun u => (columns n).flatMap fun v => forwardCellTrace M d i j u v

def dotTrace (acc : ℤ) : List (ℤ × ℤ) → List ScalarOp
  | [] => []
  | (a,b)::ys => .mul a b :: .add acc (a*b) :: dotTrace (acc+a*b) ys

theorem dotTrace_length (acc : ℤ) (ys : List (ℤ × ℤ)) : (dotTrace acc ys).length = 2*ys.length := by
  induction ys generalizing acc with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨a,b⟩ := y
    simp [dotTrace, ih]
    omega

def backwardTrace {m n : ℕ} (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n) : List ScalarOp :=
  .mul x.denominator (M i none) :: dotTrace 0
    ((List.finRange n).map fun v => (M i (some (j.succAbove v)), x.numerator v)) ++
    [.sub (x.denominator * M i none) ((List.finRange n).foldl
      (fun s v => s+M i (some (j.succAbove v))*x.numerator v) 0),
     .exactDiv (backwardDividend M i j x) (M i (some j))]

/-- The scalar trace in execution order. Both searches record exactly their
visited prefix. The remaining events are the operations on individual
entries and the successive accumulators used in back substitution. -/
def arithmeticTrace : (m n : ℕ) → IntegerAugment m n → ℤ → List ScalarOp
  | 0, _, _, _ => []
  | _+1, 0, M, _ => zeroTrace M
  | m+1, n+1, M, d =>
    pivotTrace M ++ match integerPivot M with
    | none => zeroTrace M
    | some (i,j) =>
      let M' := forwardStep M d i j
      let p := M i (some j)
      let sub := runInt m n M' p
      forwardTrace M d i j ++ arithmeticTrace m n M' p ++
        (sub.result.toList.flatMap fun x => backwardTrace M i j x)

theorem forwardTrace_length {m n : ℕ} (M : IntegerAugment (m+1) (n+1)) (d : ℤ)
    (i : Fin (m+1)) (j : Fin (n+1)) : (forwardTrace M d i j).length = 4*m*(n+1) := by
  have hrow (u : Fin m) (l : List (Option (Fin n))) :
      (l.flatMap (forwardCellTrace M d i j u)).length = 4*l.length := by
    induction l with
    | nil => simp
    | cons v l ih =>
      simp only [List.flatMap_cons, List.length_append, ih, forwardCellTrace,
        List.length_cons, List.length_nil, Nat.mul_add]
      omega
  have hcolumns : (columns n).length = n+1 := by simp [columns]
  simp only [forwardTrace, List.length_flatMap, hrow, hcolumns]
  simp [Nat.mul_comm, Nat.mul_left_comm]

theorem backwardTrace_length {m n : ℕ} (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n) : (backwardTrace M i j x).length = 2*n+3 := by
  simp [backwardTrace, dotTrace_length]

theorem arithmeticTrace_length (m n : ℕ) (M : IntegerAugment m n) (d : ℤ) :
    (arithmeticTrace m n M d).length = (runInt m n M d).operations := by
  induction m generalizing n d with
  | zero => rfl
  | succ m ih =>
    cases n with
    | zero => simp [arithmeticTrace, runInt, zeroTrace]
    | succ n =>
      rw [arithmeticTrace, runInt]
      dsimp only [integerPivot]
      cases hp : (pivotScan M).found with
      | none => simp [pivotTrace, zeroTrace]
      | some p =>
        obtain ⟨i,j⟩ := p
        dsimp only
        simp only [List.length_append, pivotTrace, List.length_map, forwardTrace_length, ih]
        cases (runInt m n (forwardStep M d i j) (M i (some j))).result <;>
          simp [backwardTrace_length, Nat.add_assoc]

def solveIntTrace {m n : ℕ} (Z : IntegerAugment m n) : List ScalarOp :=
  arithmeticTrace m n (denseAugment Z) 1

theorem solveIntTrace_length {m n : ℕ} (Z : IntegerAugment m n) :
    (solveIntTrace Z).length = (solveIntScaled Z).operations := arithmeticTrace_length ..

end Reconstruction.BareissSolver
