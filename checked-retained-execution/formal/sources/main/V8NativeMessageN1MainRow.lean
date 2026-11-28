import V8NativeMessageN1MainNorm
import V8NativeMessageC3NativeAssemblyN2MainClone
import V8NativeMessageC3MainDenominator

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

/-! Exact original MAIN positive-node substitution and common denominator.
Only actual four-copy literal occurrences are constrained. -/
namespace V8NativeMessage.N1
open scoped Classical BigOperators Polynomial
open Polynomial V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}

abbrev Occ {W : Type*} (F : Finset (W×W)) := W ⊕ ((F×Bool) ⊕ (Clone W×Bool))

def occClause : Occ F→Clause F
  | .inl v => .inl v
  | .inr (.inl (e,_)) => .inr (.inl e)
  | .inr (.inr (i,_)) => .inr (.inr i)

def occVar (hreg : ∀ v, GraphCutMoments.degree F v=3) : Occ F→Clone W
  | .inl v => (v,0)
  | .inr (.inl (e,b)) => if b then (e.val.1,MainClonedCNF.leftSlot F hreg e)
      else (e.val.2,MainClonedCNF.rightSlot F hreg e)
  | .inr (.inr ((v,i),b)) => if b then (v,i) else (v,i+1)

def δ (R Q : ℕ) : ℕ := (R-1).factorial*Q.factorial

theorem δ_pos (R Q : ℕ) : 0<δ R Q := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)

def intToRat : ℤ[X]→+*ℚ[X] := Polynomial.mapRingHom (Int.castRingHom ℚ)

def row (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (o : Occ F) (v : Clone W) : ℚ[X] :=
  L.replacement (occClause o) (occVar hreg o) v

/-- The integer common denominator and the per-coefficient magnitude bound
of MAIN Definition layout 4–5, limited to true literal rows. These are
source data/guards, not a new row-generation theorem. -/
structure RowBound (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R BP : ℕ) : Prop where
  degree : ∀ o v, (row L hreg o v).natDegree≤R
  scaled : ∀ o v j, ∃ a : ℤ, (a:ℚ)=(C (δ R Q:ℚ)*row L hreg o v).coeff j ∧ a.natAbs≤2^BP

theorem row_lift_exists (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    {R BP : ℕ} (H : RowBound L hreg R BP) (o : Occ F) (v : Clone W) :
    ∃ p : ℤ[X], intToRat p = C (δ R Q : ℚ) * row L hreg o v := by
  exact V8NativeMessage.C3.RawMain.integer_coeffs_lift _
    (fun j => let ⟨a,ha,_⟩ := H.scaled o v j; ⟨a,ha⟩)

variable (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
variable {R BP : ℕ} (H : RowBound L hreg R BP)

def irow (o : Occ F) (v : Clone W) : ℤ[X] := Classical.choose (row_lift_exists L hreg H o v)

theorem map_irow (o : Occ F) (v : Clone W) :
    intToRat (irow L hreg H o v)=C (δ R Q:ℚ)*row L hreg o v :=
  Classical.choose_spec (row_lift_exists L hreg H o v)

theorem irow_degree (o : Occ F) (v : Clone W) : (irow L hreg H o v).natDegree≤R := by
  have he : (intToRat (irow L hreg H o v)).natDegree=(irow L hreg H o v).natDegree := by
    apply Polynomial.natDegree_map_eq_of_injective
    exact Int.cast_injective
  rw [← he,map_irow]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (H.degree o v)

theorem irow_norm (o : Occ F) (v : Clone W) : coeffNorm (irow L hreg H o v)≤(R+1)*2^BP := by
  apply norm_bound_degree _ _ _ (irow_degree L hreg H o v)
  intro j
  obtain ⟨a,ha,hb⟩ := H.scaled o v j
  have he := congrArg (fun p : ℚ[X] => p.coeff j) (map_irow L hreg H o v)
  dsimp only at he
  rw [← ha] at he
  change (((irow L hreg H o v).map (Int.castRingHom ℚ)).coeff j)= (a:ℚ) at he
  rw [Polynomial.coeff_map] at he
  have he' : (irow L hreg H o v).coeff j=a := Int.cast_injective he
  rw [he']
  exact hb

def tInt : ℤ := (L.node.val:ℤ)+1

omit [DecidableEq W] in
theorem tInt_le : (tInt L).natAbs≤Q := by
  rw [show tInt L=((L.node.val+1:ℕ):ℤ) by simp [tInt],Int.natAbs_natCast]
  exact L.node.isLt

omit [DecidableEq W] in
theorem tInt_cast : (tInt L:ℚ)=nodeValue L := by simp [tInt,nodeValue]

def iBase (x : Clone W→Bool) (o : Occ F) : ℤ[X] :=
  C (∑ v : Clone W, (irow L hreg H o v).eval (tInt L)*(if x v then 1 else 0))

def iTaylor (o : Occ F) : ℤ[X] :=
  ∑ v ∈ L.U, (irow L hreg H o v).comp (C (tInt L)+X)

def iOld (o : Occ F) : ℤ[X] :=
  ∑ v ∈ L.U, C ((irow L hreg H o v).eval (tInt L))

def iTheta (x : Clone W→Bool) (o : Occ F) : ℤ[X] :=
  iBase L hreg H x o + (iTaylor L hreg H o - iOld L hreg H o)

def thetaPoly (x : Clone W→Bool) (o : Occ F) : ℚ[X] :=
  C (∑ v : Clone W, (row L hreg o v).eval (nodeValue L)*(if x v then 1 else 0)) +
    ∑ v ∈ L.U, ((row L hreg o v).comp (C (nodeValue L)+X) -
      C ((row L hreg o v).eval (nodeValue L)))

theorem thetaPoly_mk (x : Clone W→Bool) (o : Occ F) :
    (AdjoinRoot.mk _ (thetaPoly L hreg x o) : Jet J) =
      θ L x (occClause o) (occVar hreg o) := rfl

theorem map_eval_irow (o : Occ F) (v : Clone W) :
    (((irow L hreg H o v).eval (tInt L):ℤ):ℚ) =
      (δ R Q:ℚ)*(row L hreg o v).eval (nodeValue L) := by
  have he := congrArg (fun p : ℚ[X] => p.eval (nodeValue L)) (map_irow L hreg H o v)
  dsimp only at he
  rw [eval_mul,eval_C] at he
  rw [← tInt_cast L] at he
  change ((irow L hreg H o v).map (Int.castRingHom ℚ)).eval
    ((Int.castRingHom ℚ) (tInt L))=_ at he
  rw [Polynomial.eval_map,Polynomial.eval₂_hom] at he
  simpa only [tInt_cast] using he

theorem map_iTheta (x : Clone W→Bool) (o : Occ F) :
    intToRat (iTheta L hreg H x o)= C (δ R Q:ℚ)*thetaPoly L hreg x o := by
  let a : ℚ := δ R Q
  have hb : intToRat (iBase L hreg H x o) =
      C a * C (∑ v : Clone W, (row L hreg o v).eval (nodeValue L)*(if x v then 1 else 0)) := by
    unfold iBase
    change (C _).map (Int.castRingHom ℚ)=_
    rw [Polynomial.map_C,← C_mul,Finset.mul_sum,map_sum]
    apply congrArg C
    apply Finset.sum_congr rfl
    intro v _
    rw [map_mul]
    change (((irow L hreg H o v).eval (tInt L):ℤ):ℚ)*
      ((if x v then (1:ℤ) else 0:ℤ):ℚ)=_
    rw [map_eval_irow]
    cases x v <;> simp [a]
  have ht (v : Clone W) :
      intToRat ((irow L hreg H o v).comp (C (tInt L)+X)) =
        C a * (row L hreg o v).comp (C (nodeValue L)+X) := by
    change (((irow L hreg H o v).comp (C (tInt L)+X)).map (Int.castRingHom ℚ))=_
    rw [Polynomial.map_comp,Polynomial.map_add,Polynomial.map_C,Polynomial.map_X]
    change (intToRat (irow L hreg H o v)).comp (C (tInt L:ℚ)+X)=_
    rw [tInt_cast,map_irow,mul_comp,C_comp]
  have ho (v : Clone W) :
      intToRat (C ((irow L hreg H o v).eval (tInt L))) =
        C a * C ((row L hreg o v).eval (nodeValue L)) := by
    change (C _).map (Int.castRingHom ℚ)=_
    rw [Polynomial.map_C,← C_mul]
    apply congrArg C
    exact map_eval_irow L hreg H o v
  unfold iTheta iTaylor iOld thetaPoly
  rw [map_add,map_sub,hb,mul_add,Finset.mul_sum]
  simp only [map_sum,ht,ho,mul_sub,Finset.sum_sub_distrib]
  rfl


def oneEval (W : Type*) [Fintype W] (R Q BP : ℕ) : ℕ :=
  Fintype.card (Clone W)*(R+1)*2^BP*(Q+1)^R

def B₀ (W : Type*) [Fintype W] (R Q BP : ℕ) : ℕ :=
  δ R Q+3*oneEval W R Q BP

theorem node_eval_bound (o : Occ F) (v : Clone W) :
    ((irow L hreg H o v).eval (tInt L)).natAbs≤(R+1)*2^BP*(Q+1)^R :=
  (norm_eval _ _ R (Q+1) (irow_degree L hreg H o v) ((tInt_le L).trans (Nat.le_succ _))
    (Nat.succ_pos _)).trans (Nat.mul_le_mul_right _ (irow_norm L hreg H o v))

theorem shifted_row_bound (o : Occ F) (v : Clone W) :
    coeffNorm ((irow L hreg H o v).comp (C (tInt L)+X))≤(R+1)*2^BP*(Q+1)^R := by
  have hShift : coeffNorm (C (tInt L)+X)≤Q+1 := by
    apply (norm_add _ _).trans
    rw [norm_C,norm_X]
    exact Nat.add_le_add_right (tInt_le L) _
  exact (norm_comp _ _ R (Q+1) (irow_degree L hreg H o v) hShift (Nat.succ_pos _)).trans
    (Nat.mul_le_mul_right _ (irow_norm L hreg H o v))

theorem norm_iTheta (x : Clone W→Bool) (o : Occ F) :
    coeffNorm (iTheta L hreg H x o)≤3*oneEval W R Q BP := by
  let A := (R+1)*2^BP*(Q+1)^R
  have hBase : coeffNorm (iBase L hreg H x o)≤oneEval W R Q BP := by
    unfold iBase
    let f : Clone W→ℤ[X] := fun v => C ((irow L hreg H o v).eval (tInt L)*(if x v then 1 else 0))
    change coeffNorm (C (∑ v : Clone W, (irow L hreg H o v).eval (tInt L)*
      (if x v then 1 else 0)))≤_
    rw [map_sum]
    apply (norm_sum _ f).trans
    calc
      _ ≤ ∑ _v : Clone W, A := by
        apply Finset.sum_le_sum
        intro v _
        unfold f
        rw [norm_C]
        cases x v <;> simp only [Bool.false_eq_true,if_false,if_true,mul_zero,mul_one,Int.natAbs_zero]
        · exact Nat.zero_le _
        · exact node_eval_bound L hreg H o v
      _ = _ := by simp [A,oneEval,Nat.mul_assoc]
  have hU : L.U.card≤Fintype.card (Clone W) := Finset.card_le_univ _
  have hTaylor : coeffNorm (iTaylor L hreg H o)≤oneEval W R Q BP := by
    unfold iTaylor
    apply (norm_sum _ _).trans
    calc
      _ ≤ ∑ _v ∈ L.U, A := Finset.sum_le_sum fun v _ => shifted_row_bound L hreg H o v
      _ = L.U.card*A := by simp
      _ ≤ _ := by simpa only [A,oneEval,Nat.mul_assoc] using Nat.mul_le_mul_right A hU
  have hOld : coeffNorm (iOld L hreg H o)≤oneEval W R Q BP := by
    unfold iOld
    apply (norm_sum _ _).trans
    calc
      _ ≤ ∑ _v ∈ L.U, A := Finset.sum_le_sum fun v _ => by
        rw [norm_C]
        exact node_eval_bound L hreg H o v
      _ = L.U.card*A := by simp
      _ ≤ _ := by simpa only [A,oneEval,Nat.mul_assoc] using Nat.mul_le_mul_right A hU
  unfold iTheta
  have ha := norm_add (iBase L hreg H x o) (iTaylor L hreg H o-iOld L hreg H o)
  have hs := norm_sub (iTaylor L hreg H o) (iOld L hreg H o)
  omega

theorem exact_unary_norm (x : Clone W→Bool) (v : W) (positive : Bool) :
    coeffNorm (if positive then iTheta L hreg H x (.inl v)
      else C (δ R Q:ℤ)-iTheta L hreg H x (.inl v))≤B₀ W R Q BP := by
  cases positive
  · simp only [Bool.false_eq_true,if_false]
    have h := norm_sub (C (δ R Q:ℤ)) (iTheta L hreg H x (.inl v))
    rw [norm_C,Int.natAbs_natCast] at h
    exact h.trans (Nat.add_le_add_left (norm_iTheta L hreg H x (.inl v)) _)
  · simp only [if_true]
    exact (norm_iTheta L hreg H x (.inl v)).trans (Nat.le_add_left _ _)

#print axioms row_lift_exists
#print axioms map_irow
#print axioms irow_degree
#print axioms irow_norm
#print axioms thetaPoly_mk
#print axioms map_iTheta
#print axioms node_eval_bound
#print axioms shifted_row_bound
#print axioms norm_iTheta
#print axioms exact_unary_norm
end
end V8NativeMessage.N1
