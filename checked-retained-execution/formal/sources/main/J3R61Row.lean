import J3R61SourceTape

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4400000

/-! The real singleton all-one row: sum the actual coordinate constants
and take the selected coordinate's first derivative. -/
namespace J3R61
open Polynomial V8NativeMessage J3R60
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open J3R38LiteralSingleton
open scoped Polynomial BigOperators Classical
noncomputable section

def sumRow {I : Type*} (read : I → Paid (Pair ℤ)) : List I → Paid ℤ
  | [] => ⟨0,0⟩
  | i :: is =>
    let f := read i
    let s := sumRow read is
    ⟨f.value.c+s.value,f.ops+s.ops+1⟩

theorem sumRow_val {I : Type*} (read : I → Paid (Pair ℤ)) (is : List I) :
    (sumRow read is).value = (is.map (fun i => (read i).value.c)).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [sumRow, List.map_cons,List.sum_cons,ih]

theorem sumRow_ops {I : Type*} (read : I → Paid (Pair ℤ)) (is : List I) (n : ℕ)
    (h : ∀ i, (read i).ops=n) :
    (sumRow read is).ops = (n+1)*is.length := by
  induction is with
  | nil => simp [sumRow]
  | cons i is ih =>
    simp only [sumRow,h,ih,List.length_cons,Nat.mul_succ]
    omega

theorem sumRow_width {I : Type*} (read : I → Paid (Pair ℤ)) (is : List I) (w : ℕ)
    (h : ∀ i, ((read i).value.c).natAbs ≤ w) :
    (sumRow read is).value.natAbs ≤ is.length*w := by
  induction is with
  | nil => simp [sumRow]
  | cons i is ih =>
    simp only [sumRow,List.length_cons,Nat.succ_mul]
    exact (Int.natAbs_add_le ..).trans (by
      exact (Nat.add_le_add (h i) ih).trans (Nat.add_comm _ _).le)

def evalRow {I : Type*} (ord : List I) (p : I → ℚ[X]) (D R : ℕ) (t : ℤ) (i : I) :
    Paid (Pair ℤ) :=
  let read := fun j => evalCoord (p j) D R t
  let base := sumRow read ord
  let delta := read i
  ⟨⟨base.value,delta.value.d⟩,base.ops+delta.ops⟩

def rowOps (R width : ℕ) := (6*(R+1)+1)*width+6*(R+1)

theorem evalRow_ops {I : Type*} (ord : List I) (p : I → ℚ[X]) (D R : ℕ) (t : ℤ) (i : I) :
    (evalRow ord p D R t i).ops = rowOps R ord.length := by
  change (sumRow (fun j => evalCoord (p j) D R t) ord).ops+(evalCoord (p i) D R t).ops = _
  rw [sumRow_ops _ _ (6*(R+1)) (fun _ => evalCoord_ops ..),evalCoord_ops]
  rfl

theorem affine_capture_int (p : ℤ[X]) (t : ℤ) :
    capture (p.comp (C t+X)) = ⟨p.eval t,p.derivative.eval t⟩ := by
  apply Pair.ext'
  · change (p.comp (C t+X)).coeff 0 = _
    rw [coeff_zero_eq_eval_zero,eval_comp]
    simp
  · have hd (q : ℤ[X]) : q.derivative.eval 0=q.coeff 1 := by
      simp [← coeff_zero_eq_eval_zero,coeff_derivative]
    change (p.comp (C t+X)).coeff 1 = _
    rw [←hd,derivative_comp]
    simp [eval_comp]

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

def coords (W : Type*) [Fintype W] : List (Clone W) := Finset.univ.toList

def literalRow (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (i : Clone W) (o : N1.Occ F) : Paid (Pair ℤ) :=
  evalRow (coords W) (N1.row L hreg o) (printedScale R Q).value R (N1.tInt L) i

theorem literalRow_same_itheta (L : CloneTuple F r Q J) (bounds : N1.RowBound L hreg R BP)
    (i : Clone W) (hi : L.U={i}) (o : N1.Occ F) :
    (literalRow L hreg R i o).value = capture (N1.iTheta L hreg bounds (fun _ => true) o) := by
  unfold literalRow
  rw [(printedScale_exact R Q).1]
  let read : Clone W → Paid (Pair ℤ) := fun j =>
    evalCoord (N1.row L hreg o j) (N1.δ R Q) R (N1.tInt L)
  have he (j : Clone W) : (read j).value =
      ⟨(N1.irow L hreg bounds o j).eval (N1.tInt L),
       (N1.irow L hreg bounds o j).derivative.eval (N1.tInt L)⟩ :=
    exact_coordinate_horner L bounds o j
  have cc : (sumRow read (coords W)).value =
      ∑ j, (N1.irow L hreg bounds o j).eval (N1.tInt L) := by
    rw [sumRow_val]
    simp_rw [he]
    exact Finset.sum_map_toList _ _
  let p := N1.irow L hreg bounds o i
  have hc := congrArg Pair.c (affine_capture_int p (N1.tInt L))
  have hd := congrArg Pair.d (affine_capture_int p (N1.tInt L))
  have hc' : (p.comp (C (N1.tInt L)+X)).coeff 0 = p.eval (N1.tInt L) := hc
  have hd' : (p.comp (C (N1.tInt L)+X)).coeff 1 = p.derivative.eval (N1.tInt L) := hd
  ext
  · change (sumRow read (coords W)).value = _
    rw [cc]
    simp only [capture,N1.iTheta,N1.iBase,N1.iTaylor,N1.iOld,hi,Finset.sum_singleton,
      if_true,mul_one,coeff_add,coeff_sub,coeff_C_zero]
    change _ = _ + ((p.comp (C (N1.tInt L)+X)).coeff 0 - p.eval (N1.tInt L))
    rw [hc',sub_self,add_zero]
  · change (read i).value.d = _
    rw [he]
    simp only [capture,N1.iTheta,N1.iBase,N1.iTaylor,N1.iOld,hi,Finset.sum_singleton,
      if_true,mul_one,coeff_add,coeff_sub,coeff_C,one_ne_zero,if_false,zero_add,sub_zero]
    exact hd'.symm

theorem literalRow_ops (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (i : Clone W) (o : N1.Occ F) :
    (literalRow L hreg R i o).ops = rowOps R (4*Fintype.card W) := by
  unfold literalRow
  rw [evalRow_ops]
  simp [coords,Clone,Nat.mul_comm]

theorem literalRow_width (L : CloneTuple F r Q J) (bounds : N1.RowBound L hreg R BP)
    (i : Clone W) (o : N1.Occ F) :
    (literalRow L hreg R i o).value.intSize ≤
      (4*Fintype.card W+1)*hornerCap Q (2^BP) (R+1) := by
  let w := hornerCap Q (2^BP) (R+1)
  unfold literalRow
  rw [(printedScale_exact R Q).1]
  let read : Clone W → Paid (Pair ℤ) := fun j =>
    evalCoord (N1.row L hreg o j) (N1.δ R Q) R (N1.tInt L)
  have hsz (j : Clone W) : (read j).value.intSize ≤ w := by
    simpa only [read,evalCoord,List.drop_zero] using actual_coordinate_horner_width L bounds o j 0
  have h1 := sumRow_width read (coords W) w (fun j =>
    (Nat.le_add_right _ _).trans (hsz j))
  have h2 : (read i).value.d.natAbs ≤ w := (Nat.le_add_left _ _).trans (hsz i)
  change (sumRow read (coords W)).value.natAbs + (read i).value.d.natAbs ≤ _
  apply (Nat.add_le_add h1 h2).trans
  rw [show (coords W).length=4*Fintype.card W by simp [coords,Clone,Nat.mul_comm]]
  change (4*Fintype.card W)*w+w ≤ (4*Fintype.card W+1)*w
  exact le_of_eq (by ring)

#print axioms sumRow_val
#print axioms evalRow_ops
#print axioms affine_capture_int
#print axioms literalRow_same_itheta
#print axioms literalRow_ops
#print axioms literalRow_width

end
end J3R61
