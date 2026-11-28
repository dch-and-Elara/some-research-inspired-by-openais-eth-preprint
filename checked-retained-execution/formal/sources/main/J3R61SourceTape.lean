import J3R61Horner
import V8NativeMessageN1MainHeight
import J3R60NormalizeHeight

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

/-! Lift the actual rational replacement coefficients by the printed
common denominator, one exact integer quotient and multiplication each.
The Horner loop works on these produced integers, not a supplied chosen
integer polynomial. -/
namespace J3R61
open Polynomial V8NativeMessage J3R60
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber

def scaledCoefficient (D : ℕ) (q : ℚ) : ℤ := q.num * (D / q.den : ℕ)

theorem scaledCoefficient_exact (D : ℕ) (q : ℚ) (h : q.den ∣ D) :
    ((scaledCoefficient D q : ℤ) : ℚ) = (D : ℚ)*q := by
  have he : q.den*(D/q.den) = D := by rw [mul_comm]; exact Nat.div_mul_cancel h
  unfold scaledCoefficient
  rw [Int.cast_mul,Int.cast_natCast]
  rw [← rat_den_mul_value q]
  calc
    _ = ((q.den : ℚ)*(↑(D/q.den) : ℚ))*q := by ring
    _ = _ := by rw [← Nat.cast_mul, he]

def factorialLoop : ℕ → Paid ℕ
  | 0 => ⟨1,0⟩
  | n+1 =>
    let v := factorialLoop n
    ⟨(n+1)*v.value,v.ops+1⟩

theorem factorialLoop_exact (n : ℕ) :
    (factorialLoop n).value=n.factorial ∧ (factorialLoop n).ops=n := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simp only [factorialLoop,ih.1,ih.2,Nat.factorial_succ,and_self]

def printedScale (R Q : ℕ) : Paid ℕ :=
  let a := factorialLoop (R-1)
  let b := factorialLoop Q
  ⟨a.value*b.value,a.ops+b.ops+1⟩

theorem printedScale_exact (R Q : ℕ) :
    (printedScale R Q).value=N1.δ R Q ∧ (printedScale R Q).ops=(R-1)+Q+1 := by
  simp only [printedScale,(factorialLoop_exact _).1,(factorialLoop_exact _).2,N1.δ,and_self]

noncomputable section
open scoped Polynomial Classical

def coeffTape (p : ℚ[X]) (D R : ℕ) : List ℤ :=
  List.ofFn (fun j : Fin (R+1) => scaledCoefficient D (p.coeff j.val))

def evalCoord (p : ℚ[X]) (D R : ℕ) (t : ℤ) : Paid (Pair ℤ) :=
  let cs := coeffTape p D R
  let h := horner t cs
  ⟨h.value,2*cs.length+h.ops⟩

theorem evalCoord_ops (p : ℚ[X]) (D R : ℕ) (t : ℤ) :
    (evalCoord p D R t).ops = 6*(R+1) := by
  simp only [evalCoord,horner_actual_ops,coeffTape,List.length_ofFn]
  ring

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

theorem actual_scaled_coefficient (L : CloneTuple F r Q J)
    (bounds : N1.RowBound L hreg R BP) (o : N1.Occ F) (v : Clone W) (j : ℕ) :
    scaledCoefficient (N1.δ R Q) ((N1.row L hreg o v).coeff j) =
      (N1.irow L hreg bounds o v).coeff j := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z:ℚ)))
  rw [scaledCoefficient_exact _ _ (N1.row_coefficient_height L hreg bounds o v j).1]
  have h := congrArg (fun p : ℚ[X] => p.coeff j) (N1.map_irow L hreg bounds o v)
  change (((N1.irow L hreg bounds o v).map (Int.castRingHom ℚ)).coeff j) =
    (C (N1.δ R Q:ℚ)*N1.row L hreg o v).coeff j at h
  rw [Polynomial.coeff_map, coeff_C_mul] at h
  exact h.symm

theorem actual_scaled_coefficient_width (L : CloneTuple F r Q J)
    (bounds : N1.RowBound L hreg R BP) (o : N1.Occ F) (v : Clone W) (j : ℕ) :
    let q := (N1.row L hreg o v).coeff j
    q.den ∣ N1.δ R Q ∧ q.num.natAbs ≤ 2^BP ∧
      N1.δ R Q / q.den ≤ N1.δ R Q ∧
      (scaledCoefficient (N1.δ R Q) q).natAbs ≤ 2^BP := by
  dsimp only
  have h := N1.row_coefficient_height L hreg bounds o v j
  refine ⟨h.1,h.2,Nat.div_le_self _ _,?_⟩
  obtain ⟨a,ha,hw⟩ := bounds.scaled o v j
  have eq : scaledCoefficient (N1.δ R Q) ((N1.row L hreg o v).coeff j)=a := by
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z:ℚ)))
    rw [scaledCoefficient_exact _ _ h.1,ha,coeff_C_mul]
  rw [eq]
  exact hw

theorem tape_is_actual_irow (L : CloneTuple F r Q J) (bounds : N1.RowBound L hreg R BP)
    (o : N1.Occ F) (v : Clone W) :
    tapePoly (coeffTape (N1.row L hreg o v) (N1.δ R Q) R) = N1.irow L hreg bounds o v := by
  ext k
  rw [tapePoly_coeff]
  by_cases hk : k < R+1
  · simp only [coeffTape,List.getElem?_ofFn,hk,dif_pos,Option.getD_some]
    exact actual_scaled_coefficient L bounds o v k
  · have hzero := coeff_eq_zero_of_natDegree_lt
      ((N1.irow_degree L hreg bounds o v).trans_lt (by omega : R < k))
    simp only [coeffTape,List.getElem?_ofFn,dif_neg hk,Option.getD_none,hzero]

theorem exact_coordinate_horner (L : CloneTuple F r Q J)
    (bounds : N1.RowBound L hreg R BP) (o : N1.Occ F) (v : Clone W) :
    (evalCoord (N1.row L hreg o v) (N1.δ R Q) R (N1.tInt L)).value =
      ⟨(N1.irow L hreg bounds o v).eval (N1.tInt L),
        (N1.irow L hreg bounds o v).derivative.eval (N1.tInt L)⟩ := by
  simp only [evalCoord,horner_actual_coeffs,tape_is_actual_irow L bounds]

theorem actual_coordinate_horner_width (L : CloneTuple F r Q J)
    (bounds : N1.RowBound L hreg R BP) (o : N1.Occ F) (v : Clone W) (k : ℕ) :
    (horner (N1.tInt L) ((coeffTape (N1.row L hreg o v) (N1.δ R Q) R).drop k)).value.intSize
      ≤ hornerCap Q (2^BP) (R+1) := by
  apply horner_actual_suffix_width _ _ _ _ _ (N1.tInt_le L)
  · intro a ha
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp ha
    rw [← hj]
    exact (actual_scaled_coefficient_width L bounds o v j.val).2.2.2
  · simp only [coeffTape,List.length_ofFn,le_rfl]

#print axioms scaledCoefficient_exact
#print axioms printedScale_exact
#print axioms evalCoord_ops
#print axioms actual_scaled_coefficient
#print axioms actual_scaled_coefficient_width
#print axioms tape_is_actual_irow
#print axioms exact_coordinate_horner
#print axioms actual_coordinate_horner_width

end
end J3R61
