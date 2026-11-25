import AffineCompileExpr

namespace AffineCompile

open AffineEdge AffineCost
open AffineCost.Bit (Run)

variable {q : ℕ}

/-- Construct the same recursive product-coefficient tree, charging each
branch, index predecessor, and emitted node. -/
def nodeCoeffRun : List (Fin q) → ℕ → Run (Expr q)
  | [], k => ⟨.bit (match k with | 0 => true | _+1 => false), 16⟩
  | s :: ss, 0 =>
    let a := nodeCoeffRun ss 0
    ⟨.mul (.neg (.site s)) a.value, 32+a.steps⟩
  | s :: ss, k+1 =>
    let a := nodeCoeffRun ss k
    let b := nodeCoeffRun ss (k+1)
    ⟨.add a.value (.mul (.neg (.site s)) b.value), 64+a.steps+b.steps⟩

@[simp] theorem nodeCoeffRun_value (is : List (Fin q)) (k : ℕ) :
    (nodeCoeffRun is k).value = Expr.nodeCoeff is k := by
  induction is generalizing k <;> cases k <;> simp [nodeCoeffRun, Expr.nodeCoeff, *]

theorem nodeCoeffRun_steps (is : List (Fin q)) (k : ℕ) :
    (nodeCoeffRun is k).steps+64 ≤ 80*2^is.length := by
  induction is generalizing k with
  | nil => cases k <;> simp [nodeCoeffRun]
  | cons s ss ih =>
    cases k with
    | zero =>
      have h := ih 0
      have hp : 0 < 2^ss.length := Nat.pow_pos (by decide)
      simp only [nodeCoeffRun, List.length_cons, pow_succ]
      omega
    | succ k =>
      have h := ih k
      have h' := ih (k+1)
      simp only [nodeCoeffRun, List.length_cons, pow_succ]
      omega

def negProductRun : List (Fin q) → Run (Expr q)
  | [] => emit (.bit true)
  | t :: ts =>
    let r := negProductRun ts
    ⟨.mul (.neg (.site t)) r.value, 32+r.steps⟩

@[simp] theorem negProductRun_value (is : List (Fin q)) :
    (negProductRun is).value = Expr.negLabelProduct is := by
  induction is <;> simp [negProductRun, Expr.negLabelProduct, emit, *]

theorem negProductRun_steps (is : List (Fin q)) :
    (negProductRun is).steps = 8+32*is.length := by
  induction is <;> simp [negProductRun, emit, *, Nat.mul_succ]; omega

def sumBuild {A : Type} (f : A → Run (Expr q)) : List A → Run (Expr q)
  | [] => emit (.bit false)
  | a :: as =>
    let x := f a
    let y := sumBuild f as
    ⟨.add x.value y.value, 16+x.steps+y.steps⟩

@[simp] theorem sumBuild_value {A : Type} (f : A → Run (Expr q)) (xs : List A) :
    (sumBuild f xs).value = Expr.sum (xs.map fun a => (f a).value) := by
  induction xs <;> simp [sumBuild, Expr.sum, emit, *]

theorem sumBuild_steps {A : Type} (f : A → Run (Expr q)) (xs : List A) (C : ℕ)
    (hc : ∀ a ∈ xs, (f a).steps ≤ C) :
    (sumBuild f xs).steps ≤ 8+xs.length*(16+C) := by
  induction xs with
  | nil => simp [sumBuild, emit]
  | cons a as ih =>
    have ha := hc a (by simp)
    have ht := ih (fun a ha => hc a (by simp [ha]))
    simp only [sumBuild, List.length_cons, Nat.add_mul, one_mul]
    omega

def exceptRun (is : List (Fin q)) (t : Fin q) : Run (List (Fin q)) :=
  filterList (fun i =>
    let e := indexEq i.val t.val
    ⟨!e.value,8+e.steps⟩) is

@[simp] theorem exceptRun_value (t : Fin q) :
    (exceptRun (List.finRange q) t).value = exceptList t := by
  simp only [exceptRun, filterList_value, indexEq_value, exceptList]
  apply List.filter_congr
  intro i _
  change (!(i.val == t.val)) = (!(i == t))
  apply congrArg (!·)
  exact Bool.eq_iff_iff.mpr (by simp [beq_iff_eq, Fin.ext_iff])

theorem exceptRun_length (is : List (Fin q)) (t : Fin q) :
    (exceptRun is t).value.length ≤ is.length := by
  unfold exceptRun
  rw [filterList_value]
  exact List.length_filter_le _ _

theorem exceptRun_steps (is : List (Fin q)) (hi : is.length ≤ q) (t : Fin q) :
    (exceptRun is t).steps ≤ 64*(q+1)^2 := by
  have h := filterList_steps
    (fun i : Fin q => let e := indexEq i.val t.val; ⟨!e.value,8+e.steps⟩) is (24*(q+1))
    (fun i _ => by
      have h := indexEq_steps i.val t.val
      have hlt := i.isLt
      dsimp
      omega)
  have hm := Nat.mul_le_mul_right (16+24*(q+1)) hi
  simp only [exceptRun]
  nlinarith only [h, hm]

def termRun (is : List (Fin q)) (u v : CellWord) (k t : Fin q) : Run (Expr q) :=
  let l := localCells is u v t
  let r := exceptRun is t
  let y := nodeCoeffRun r.value k.val
  ⟨.mul (.mul (.site t) l.value) y.value, 32+l.steps+r.steps+y.steps⟩

@[simp] theorem termRun_value (u v : CellWord) (k t : Fin q) :
    (termRun (List.finRange q) u v k t).value =
      .mul (.mul (.site t) (localExpr (decodeWord q u) (decodeWord q v) t))
        (Expr.nodeCoeff (exceptList t) k.val) := by
  simp [termRun]

theorem termRun_steps (is : List (Fin q)) (hi : is.length ≤ q) (u v : CellWord) (k t : Fin q) :
    (termRun is u v k t).steps ≤ 9000*(q+1)^2+80*2^q := by
  have h1 := localCells_steps is hi u v t
  have h2 := exceptRun_steps is hi t
  have h3 := nodeCoeffRun_steps (exceptRun is t).value k.val
  have he := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
    ((exceptRun_length is t).trans hi)
  simp only [termRun]
  nlinarith only [h1,h2,h3,he]

/-- Construct every node of the coefficient syntax from two explicit bit
strings and bounded indices. No field values enter this program. -/
def coefficientCells (is : List (Fin q)) (u v : CellWord) (k : Fin q) : Run (Expr q) :=
  let ab := pairCells is u v
  let ea := indexEq k.val 0
  let eb := indexEq k.val q.pred
  let p := negProductRun is
  let s := sumBuild (termRun is u v k) is
  let a := if ea.value then ab.value.1 else Expr.bit false
  let b := if eb.value then ab.value.2 else Expr.bit false
  ⟨.add a (.mul (.inv (.neg p.value)) (.add b s.value)),
    128+ab.steps+ea.steps+eb.steps+p.steps+s.steps⟩

@[simp] theorem coefficientCells_value (u v : CellWord) (k : Fin q) :
    (coefficientCells (List.finRange q) u v k).value =
      coefficientExpr (decodeWord q u) (decodeWord q v) k := by
  simp only [coefficientCells, coefficientExpr, pairCells_value, indexEq_value, negProductRun_value,
    sumBuild_value, termRun_value, List.ofFn_eq_map, Nat.pred_eq_sub_one, beq_iff_eq]

def coefficientGenerationBound (D q : ℕ) : ℕ :=
  16384*(q+1)^3+128*(q+1)*D

theorem coefficientCells_steps (is : List (Fin q)) (hi : is.length ≤ q) (u v : CellWord)
    (k : Fin q) : (coefficientCells is u v k).steps ≤ coefficientGenerationBound (4^q) q := by
  have h1 := pairCells_steps is hi u v
  have h2 := indexEq_steps k.val 0
  have h3 := indexEq_steps k.val q.pred
  have hk := k.isLt
  have h4 := negProductRun_steps is
  have h5 := sumBuild_steps (termRun is u v k) is (9000*(q+1)^2+80*2^q)
    (fun t _ => termRun_steps is hi u v k t)
  have hm := Nat.mul_le_mul_right (16+(9000*(q+1)^2+80*2^q)) hi
  have he : 2^q ≤ 4^q := Nat.pow_le_pow_left (by decide) _
  have hqpow := Nat.mul_le_mul_left q he
  have hs : 1 ≤ (q+1)^2 := Nat.pow_pos (by omega)
  have hD : 1 ≤ 4^q := Nat.pow_pos (by decide)
  have hlin : q+1 ≤ (q+1)^2 := by
    rw [pow_two]
    simpa only [one_mul] using Nat.mul_le_mul_right (q+1) (show 1 ≤ q+1 by omega)
  have hquad : (q+1)^2 ≤ (q+1)^3 := by
    rw [show (3:ℕ) = 2+1 by decide, pow_succ]
    simpa only [mul_one] using Nat.mul_le_mul_left ((q+1)^2) (show 1 ≤ q+1 by omega)
  have hcubic : q*(q+1)^2 ≤ (q+1)^3 := calc
    _ ≤ (q+1)*(q+1)^2 := Nat.mul_le_mul_right _ (Nat.le_succ q)
    _ = _ := by ring
  simp only [coefficientCells, coefficientGenerationBound]
  nlinarith only [h1,h2,h3,h4,h5,hm,hk,hi,he,hqpow,hs,hD,hlin,hquad,hcubic]

/-- Copy the descriptor tree without assuming shared subtrees are free to
materialize. The label of a site remains a bounded index. -/
def materialize : Expr q → Run (Expr q)
  | .bit b => ⟨.bit b,16⟩
  | .site t => ⟨.site t,16⟩
  | .neg a => let r := materialize a; ⟨.neg r.value,16+r.steps⟩
  | .inv a => let r := materialize a; ⟨.inv r.value,16+r.steps⟩
  | .add a b =>
    let x := materialize a
    let y := materialize b
    ⟨.add x.value y.value,16+x.steps+y.steps⟩
  | .mul a b =>
    let x := materialize a
    let y := materialize b
    ⟨.mul x.value y.value,16+x.steps+y.steps⟩

@[simp] theorem materialize_value (e : Expr q) : (materialize e).value = e := by
  induction e <;> simp [materialize, *]

theorem materialize_steps (e : Expr q) : (materialize e).steps = 16*e.nodes := by
  induction e <;> simp [materialize, Expr.nodes, Nat.mul_add, *] <;> omega

end AffineCompile
