import AffineCompilePrimitives
import AffineCostCoefficients

namespace AffineCompile

open AffineEdge AffineCost
open AffineCost.Bit (Run)

abbrev CellWord := Cells × Cells

def decodeBits (q : ℕ) (xs : Cells) : Bits q := fun t => (xs[t.val]?).getD false

def decodeWord (q : ℕ) (w : CellWord) : Word q :=
  (decodeBits q w.1, decodeBits q w.2)

private theorem readFin_steps {q : ℕ} (xs : Cells) (t : Fin q) :
    (readCell xs t.val).steps ≤ 16*(q+1) := by
  have := readCell_steps xs t.val
  have := t.isLt
  omega

variable {q : ℕ}

def agreeAt (u v : CellWord) (t : Fin q) : Run Bool :=
  let a := readCell v.1 t.val
  let b := readCell u.2 t.val
  ⟨a.value == b.value, 8+a.steps+b.steps⟩

def scanCells (is : List (Fin q)) (u v : CellWord) : Run (Match q) :=
  let r := filterList (agreeAt u v) is
  ⟨Match.ofList r.value, 16+r.steps⟩

@[simp] theorem scanCells_value (u v : CellWord) :
    (scanCells (List.finRange q) u v).value = scan (decodeWord q u) (decodeWord q v) := by
  simp [scanCells, agreeAt, scan, decodeWord, decodeBits]

theorem scanCells_steps (is : List (Fin q)) (hi : is.length ≤ q) (u v : CellWord) :
    (scanCells is u v).steps ≤ 256*(q+1)^2 := by
  have h := filterList_steps (agreeAt u v) is (48*(q+1)) (fun t _ => by
    have h1 := readFin_steps v.1 t
    have h2 := readFin_steps u.2 t
    simp only [agreeAt]
    omega)
  have hm := Nat.mul_le_mul_right (16+48*(q+1)) hi
  simp only [scanCells]
  nlinarith only [h, hm]

def equalAt (u v : CellWord) (t : Fin q) : Run Bool :=
  let a := readCell u.1 t.val
  let b := readCell u.2 t.val
  let c := readCell v.1 t.val
  let d := readCell v.2 t.val
  ⟨(a.value == c.value) && (b.value == d.value), 16+a.steps+b.steps+c.steps+d.steps⟩

def equalCells (is : List (Fin q)) (u v : CellWord) : Run Bool := allList (equalAt u v) is

@[simp] theorem equalCells_value (u v : CellWord) :
    (equalCells (List.finRange q) u v).value = wordEqual (decodeWord q u) (decodeWord q v) := by
  simp [equalCells, equalAt, wordEqual, decodeWord, decodeBits]

theorem equalCells_steps (is : List (Fin q)) (hi : is.length ≤ q) (u v : CellWord) :
    (equalCells is u v).steps ≤ 256*(q+1)^2 := by
  have h := allList_steps (equalAt u v) is (80*(q+1)) (fun t _ => by
    have h1 := readFin_steps u.1 t
    have h2 := readFin_steps u.2 t
    have h3 := readFin_steps v.1 t
    have h4 := readFin_steps v.2 t
    simp only [equalAt]
    omega)
  have hm := Nat.mul_le_mul_right (16+80*(q+1)) hi
  simp only [equalCells]
  nlinarith only [h, hm]

private def oddRun {A : Type} (f : A → Run Bool) : List A → Run Bool
  | [] => emit false
  | a :: as =>
    let x := f a
    let y := oddRun f as
    ⟨xor x.value y.value, 16+x.steps+y.steps⟩

private theorem xor_parity (b : Bool) (n : ℕ) :
    xor b (decide (n%2=1)) = decide ((bitScalar (R := ℕ) b+n)%2=1) := by
  cases b
  · simp [bitScalar]
  · simp only [bitScalar, if_true]
    by_cases h : n%2 = 1
    · have hh : ¬ (1+n)%2=1 := by omega
      simp [h,hh]
    · have hh : (1+n)%2=1 := by omega
      simp [h,hh]

private theorem oddRun_value {A : Type} (f : A → Run Bool) (as : List A) :
    (oddRun f as).value =
      decide (((as.map fun a => bitScalar (R := ℕ) (f a).value).sum)%2=1) := by
  induction as with
  | nil => simp [oddRun, emit]
  | cons a as ih =>
    simp only [oddRun, List.map_cons, List.sum_cons, ih]
    exact xor_parity _ _

private theorem oddRun_steps {A : Type} (f : A → Run Bool) (as : List A) (C : ℕ)
    (hc : ∀ a ∈ as, (f a).steps ≤ C) :
    (oddRun f as).steps ≤ 8+as.length*(16+C) := by
  induction as with
  | nil => simp [oddRun, emit]
  | cons a as ih =>
    have ha := hc a (by simp)
    have ht := ih (fun x hx => hc x (by simp [hx]))
    simp only [oddRun, List.length_cons, Nat.add_mul, one_mul]
    omega

def parityCells (is : List (Fin q)) (flip : Bool) (xs : Cells) : Run Bool :=
  oddRun (fun t =>
    let r := readCell xs t.val
    ⟨xor flip r.value, 8+r.steps⟩) is

@[simp] theorem parityCells_value (flip : Bool) (xs : Cells) :
    (parityCells (List.finRange q) flip xs).value =
      parityBits (fun t => xor flip (decodeBits q xs t)) := by
  simp only [parityCells, oddRun_value, readCell_value, decodeBits]
  unfold parityBits
  rw [List.ofFn_eq_map]

theorem parityCells_steps (is : List (Fin q)) (hi : is.length ≤ q) (flip : Bool) (xs : Cells) :
    (parityCells is flip xs).steps ≤ 256*(q+1)^2 := by
  have h := oddRun_steps
    (fun t : Fin q => let r := readCell xs t.val; ⟨xor flip r.value,8+r.steps⟩)
    is (24*(q+1)) (fun t _ => by
      have hh := readFin_steps xs t
      dsimp
      omega)
  have hm := Nat.mul_le_mul_right (16+24*(q+1)) hi
  simp only [parityCells]
  nlinarith only [h, hm]

def partnerRun (t : Fin q) : Run (Option (Fin q)) :=
  let half := indexHalf t.val
  let j := if half.value.2 then t.val.pred else t.val+1
  let lt := indexLt j q
  ⟨if h : lt.value = true then some ⟨j, of_decide_eq_true ((indexLt_value j q).symm ▸ h)⟩ else none,
    32+half.steps+lt.steps⟩

@[simp] theorem partnerRun_value (t : Fin q) : (partnerRun t).value = partner t := by
  by_cases h : t.val%2 = 0
  · simp [partnerRun, partner, h]
  · have hy : t.val%2 = 1 := by omega
    simp [partnerRun, partner, hy, Nat.pred_eq_sub_one]

theorem partnerRun_steps (t : Fin q) : (partnerRun t).steps ≤ 64*(q+1) := by
  let j := if (indexHalf t.val).value.2 then t.val.pred else t.val+1
  have ht := t.isLt
  have hj : j ≤ q := by
    dsimp only [j]
    split <;> have := Nat.pred_le t.val <;> omega
  have hh := indexHalf_steps t.val
  have hlt := indexLt_steps j q
  change 32+(indexHalf t.val).steps+(indexLt j q).steps ≤ _
  omega

def bucketEqRun (s t : Fin q) : Run Bool :=
  let a := indexHalf s.val
  let b := indexHalf t.val
  let e := indexEq a.value.1 b.value.1
  ⟨e.value, 8+a.steps+b.steps+e.steps⟩

@[simp] theorem bucketEqRun_value (s t : Fin q) :
    (bucketEqRun s t).value = decide (bucket s = bucket t) := by
  by_cases h : s.val/2 = t.val/2 <;>
    simp [bucketEqRun, bucket, Fin.ext_iff, h]

theorem bucketEqRun_steps (s t : Fin q) : (bucketEqRun s t).steps ≤ 64*(q+1) := by
  have h1 := indexHalf_steps s.val
  have h2 := indexHalf_steps t.val
  have h3 := indexEq_steps (indexHalf s.val).value.1 (indexHalf t.val).value.1
  simp only [indexHalf_value] at h3
  have hs := s.isLt
  have ht := t.isLt
  simp only [bucketEqRun, indexHalf_value]
  omega

/-- Scale at the complement of the second bit string, without an oracle
lookup into the decoded functional representation. -/
def scaleCells (xs : Cells) (t : Fin q) : Run (Expr q × Expr q) :=
  let b := readCell xs t.val
  let d : Expr q := Expr.sub (.bit b.value) (.bit (!b.value))
  let pr := partnerRun t
  let out := match pr.value with
    | none => (d, .bit false)
    | some s =>
      let a := Expr.mul (.mul d (.site t)) (.inv (Expr.sub (.site t) (.site s)))
      (a, .mul (.site s) a)
  ⟨out, 128+b.steps+pr.steps⟩

@[simp] theorem scaleCells_value (xs : Cells) (t : Fin q) :
    (scaleCells xs t).value = scaleExpr (complement (decodeBits q xs)) t := by
  cases h : partner t <;> simp [scaleCells, scaleExpr, complement, decodeBits, h]

theorem scaleCells_steps (xs : Cells) (t : Fin q) :
    (scaleCells xs t).steps ≤ 256*(q+1) := by
  have := readFin_steps xs t
  have := partnerRun_steps t
  simp only [scaleCells]
  omega

def pairCells (is : List (Fin q)) (u v : CellWord) : Run (Expr q × Expr q) :=
  let us := scanCells is u u
  let vs := scanCells is v v
  let out : Run (Expr q × Expr q) := match us.value, vs.value with
    | .zero, .zero =>
      let a := parityCells is true u.2
      let b := parityCells is false v.1
      ⟨(.bit (b.value == a.value), .bit false), 16+a.steps+b.steps⟩
    | .one t, .one s =>
      let e := bucketEqRun s t
      let x := readCell v.1 s.val
      let y := readCell u.2 s.val
      let r := scaleCells u.2 t
      let d : Expr q := if e.value then Expr.sub (.bit x.value) (.bit (!y.value)) else .bit false
      ⟨(.mul r.value.1 d, .mul r.value.2 d), 64+e.steps+x.steps+y.steps+r.steps⟩
    | _, _ => emit (.bit false, .bit false)
  ⟨out.value, 32+us.steps+vs.steps+out.steps⟩

@[simp] theorem pairCells_value (u v : CellWord) :
    (pairCells (List.finRange q) u v).value = pairExpr (decodeWord q u) (decodeWord q v) := by
  cases hu : scan (decodeWord q u) (decodeWord q u) <;>
    cases hv : scan (decodeWord q v) (decodeWord q v) <;>
    simp only [pairCells, scanCells_value, pairExpr, hu, hv, emit]
  · simp [decodeWord, parityCells_value, parityBits_eq] <;> rfl
  · simp [decodeWord, decodeBits, AffineEdge.complement]

theorem pairCells_steps (is : List (Fin q)) (hi : is.length ≤ q) (u v : CellWord) :
    (pairCells is u v).steps ≤ 4096*(q+1)^2 := by
  have h1 := scanCells_steps is hi u u
  have h2 := scanCells_steps is hi v v
  have hq : 1 ≤ (q+1)^2 := Nat.pow_pos (by omega)
  unfold pairCells
  dsimp only
  split
  · have h3 := parityCells_steps is hi true u.2
    have h4 := parityCells_steps is hi false v.1
    dsimp only
    nlinarith only [h1,h2,h3,h4,hq]
  · rename_i t s _ _
    have h3 := bucketEqRun_steps s t
    have h4 := readFin_steps v.1 s
    have h5 := readFin_steps u.2 s
    have h6 := scaleCells_steps u.2 t
    dsimp only
    nlinarith only [h1,h2,h3,h4,h5,h6,hq]
  · simp only [emit]
    nlinarith only [h1,h2,hq]

def localCells (is : List (Fin q)) (u v : CellWord) (i : Fin q) : Run (Expr q) :=
  let ab := pairCells is u v
  let e := equalCells is u v
  let r := Expr.sub (.bit e.value) ab.value.1
  let m := scanCells is u v
  let out : Run (Expr q) := match m.value with
    | .zero => emit (.bit false)
    | .one t =>
      let h := indexEq i.val t.val
      ⟨if h.value then r else .bit false, 16+h.steps⟩
    | .two s t =>
      let hs := indexEq i.val s.val
      let ht := indexEq i.val t.val
      let l := Expr.mul (Expr.sub (.neg ab.value.2) (.mul (.site t) r))
        (.inv (Expr.sub (.site s) (.site t)))
      ⟨if hs.value then l else if ht.value then Expr.sub r l else .bit false,
        128+hs.steps+ht.steps⟩
  ⟨out.value, 32+ab.steps+e.steps+m.steps+out.steps⟩

@[simp] theorem localCells_value (u v : CellWord) (i : Fin q) :
    (localCells (List.finRange q) u v i).value =
      localExpr (decodeWord q u) (decodeWord q v) i := by
  cases h : scan (decodeWord q u) (decodeWord q v) <;>
    simp [localCells, localExpr, h, Fin.ext_iff, emit]

theorem localCells_steps (is : List (Fin q)) (hi : is.length ≤ q) (u v : CellWord) (i : Fin q) :
    (localCells is u v i).steps ≤ 8192*(q+1)^2 := by
  have h1 := pairCells_steps is hi u v
  have h2 := equalCells_steps is hi u v
  have h3 := scanCells_steps is hi u v
  have hq : 1 ≤ (q+1)^2 := Nat.pow_pos (by omega)
  unfold localCells
  dsimp only
  split
  · simp only [emit]
    nlinarith only [h1,h2,h3,hq]
  · rename_i t _
    have h4 := indexEq_steps i.val t.val
    have hi' := i.isLt
    dsimp only
    nlinarith only [h1,h2,h3,h4,hi',hq]
  · rename_i s t _
    have h4 := indexEq_steps i.val s.val
    have h5 := indexEq_steps i.val t.val
    have hi' := i.isLt
    dsimp only
    nlinarith only [h1,h2,h3,h4,h5,hi',hq]

end AffineCompile
