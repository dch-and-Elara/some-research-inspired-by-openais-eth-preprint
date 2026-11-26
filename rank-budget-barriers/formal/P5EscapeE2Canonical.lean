import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Paper 5 §9, global canonical normalization. The nonnegative lift is
the *actual* Euclidean residue of the integer difference; we do not replace
it by an arbitrary function chosen to have high rank. -/
namespace Paper5.EscapeE2
open scoped BigOperators
open Matrix Module

def difference {I J K : Type*} [Sub K] (a : I→K) (b : J→K) : Matrix I J K :=
  Matrix.of (fun i j=>a i-b j)

theorem difference_rank_le_two {I J K : Type*} [Fintype I] [Fintype J] [Field K]
    (a : I→K) (b : J→K) : (difference a b).rank≤2 := by
  let U : Matrix I (Fin 2) K := Matrix.of fun i k=>if k=0 then a i else 1
  let V : Matrix (Fin 2) J K := Matrix.of fun k j=>if k=0 then 1 else -b j
  have h : difference a b=U*V := by
    ext i j
    simp [difference,U,V,Matrix.mul_apply,Fin.sum_univ_two,sub_eq_add_neg]
  rw [h]
  exact (Matrix.rank_mul_le_left U V).trans (by simpa using Matrix.rank_le_card_width U)

def residueInt {q : ℕ} (x y : Fin q) : ℤ := ((x.val:ℤ)-y.val)%(q:ℤ)

def canonicalMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℚ :=
  Matrix.of fun x y=>(residueInt x y : ℚ)

def integerMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℚ :=
  difference (fun x : Fin q=>(x.val:ℚ)) (fun y : Fin q=>(y.val:ℚ))

theorem integer_matrix_rank_le_two (q : ℕ) : (integerMatrix q).rank≤2 :=
  difference_rank_le_two _ _

theorem residueInt_if {q : ℕ} (x y : Fin q) :
    residueInt x y = if y.val≤x.val then (x.val:ℤ)-y.val else (x.val:ℤ)-y.val+q := by
  have hx:=x.isLt
  have hy:=y.isLt
  unfold residueInt
  split_ifs with h
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · have hm : (((x.val:ℤ)-y.val)+(q:ℤ)) % (q:ℤ)=((x.val:ℤ)-y.val)%(q:ℤ) := by simp
    rw [←hm]
    exact Int.emod_eq_of_lt (by omega) (by omega)

def predIndex {q : ℕ} (x : Fin q) : Fin q :=
  ⟨x.val-1, (Nat.sub_le _ _).trans_lt x.isLt⟩

theorem residueInt_adjacent {q : ℕ} (x : Fin q) (hx : 0<x.val) (y : Fin q) :
    residueInt x y-residueInt (predIndex x) y=if x=y then 1-(q:ℤ) else 1 := by
  rw [residueInt_if,residueInt_if]
  simp only [predIndex]
  by_cases h : x=y
  · subst y
    rw [if_pos (Nat.le_refl _),if_neg (by omega),if_pos rfl]
    omega
  · rw [if_neg h]
    have hval : x.val≠y.val := fun e=>h (Fin.ext e)
    split_ifs <;> omega

theorem canonical_adjacent {q : ℕ} (x : Fin q) (hx : 0<x.val) (y : Fin q) :
    canonicalMatrix q x y - canonicalMatrix q (predIndex x) y =
      (1:ℚ)-if x=y then (q:ℚ) else 0 := by
  have h := residueInt_adjacent x hx y
  have hu := congrArg (fun z : ℤ=>(z:ℚ)) h
  by_cases H : x=y <;> simpa [canonicalMatrix,H] using hu

def zeroIndex (q : ℕ) (hq : 0<q) : Fin q := ⟨0,hq⟩

def negIndex {q : ℕ} (hq : 0<q) (y : Fin q) : Fin q :=
  if h : y.val=0 then zeroIndex q hq else ⟨q-y.val,by have hp:=y.isLt; omega⟩

theorem negIndex_involutive {q : ℕ} (hq : 0<q) :
    Function.Involutive (negIndex hq) := by
  intro y
  apply Fin.ext
  by_cases h : y.val=0
  · simp [negIndex,zeroIndex,h]
  · have hn : q-y.val≠0 := by have hlt:=y.isLt; omega
    simp [negIndex,h,hn,Nat.sub_sub_self y.isLt.le]

def negIndexEquiv {q : ℕ} (hq : 0<q) : Fin q ≃ Fin q :=
  (negIndex_involutive hq).toPerm (negIndex hq)

theorem row_zero_perm {q : ℕ} (hq : 0<q) (y : Fin q) :
    canonicalMatrix q (zeroIndex q hq) y=((negIndex hq y).val:ℚ) := by
  unfold canonicalMatrix
  rw [Matrix.of_apply,residueInt_if]
  simp only [zeroIndex,nonpos_iff_eq_zero]
  by_cases h : y.val=0
  · simp [h,negIndex,zeroIndex]
  · simp [h,negIndex,Nat.cast_sub y.isLt.le,sub_eq_add_neg,add_comm]

theorem sum_fin_values (q : ℕ) : ∑ j : Fin q,(j.val:ℚ)=(q:ℚ)*((q:ℚ)-1)/2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last,ih,Nat.cast_succ]
    ring

theorem canonical_zero_row_sum {q : ℕ} (hq : 0<q) :
    ∑ y,canonicalMatrix q (zeroIndex q hq) y=(q:ℚ)*((q:ℚ)-1)/2 := by
  simp_rw [row_zero_perm hq]
  have he := (negIndexEquiv hq).sum_comp (fun y : Fin q=>(y.val:ℚ))
  change (∑ y : Fin q,((negIndex hq y).val:ℚ))=∑ y : Fin q,(y.val:ℚ) at he
  exact he.trans (sum_fin_values q)

theorem canonical_kernel_zero {q : ℕ} (hq : 2≤q)
    (v : Fin q→ℚ) (h : (canonicalMatrix q).mulVec v=0) : v=0 := by
  classical
  let o := zeroIndex q (by omega)
  let s := ∑ y : Fin q,v y
  let c := s/(q:ℚ)
  have hqpos : 0<(q:ℚ) := by exact_mod_cast (show 0<q by omega)
  have hv (x : Fin q) : ∑ y,canonicalMatrix q x y*v y=0 := congrFun h x
  have hd (x : Fin q) (hx : 0<x.val) : s=(q:ℚ)*v x := by
    have ht : ∑ y,(canonicalMatrix q x y-canonicalMatrix q (predIndex x) y)*v y=0 := by
      simp only [sub_mul,Finset.sum_sub_distrib,hv,sub_zero]
    simp only [canonical_adjacent x hx,sub_mul,one_mul,Finset.sum_sub_distrib,ite_mul,
      zero_mul] at ht
    have hite : (∑ y : Fin q,if x=y then (q:ℚ)*v y else 0)=(q:ℚ)*v x := by simp
    rw [hite] at ht
    exact sub_eq_zero.mp ht
  have hc (x : Fin q) (hxo : x≠o) : v x=c := by
    have hx : 0<x.val := Nat.pos_of_ne_zero (fun hz=>hxo (Fin.ext hz))
    apply (eq_div_iff hqpos.ne').mpr
    have hh := hd x hx
    linarith only [hh]
  have ht : ∑ y : Fin q,(v y-c)=0 := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul]
    change s-(q:ℚ)*c=0
    dsimp [c]
    field_simp
    ring
  have ho : v o=c := by
    rw [Finset.sum_eq_single o (fun y _ hy=>sub_eq_zero.mpr (hc y hy))
      (by simp)] at ht
    exact sub_eq_zero.mp ht
  have hall (y : Fin q) : v y=c := by
    by_cases hy : y=o
    · simpa [hy] using ho
    · exact hc y hy
  have hz := hv o
  simp only [hall,←Finset.sum_mul] at hz
  have hy : (q:ℚ)*((q:ℚ)-1)/2 ≠ 0 := by
    have h2 : (2:ℚ)≤q := by exact_mod_cast hq
    exact (div_pos (mul_pos hqpos (by linarith only [h2])) (by norm_num)).ne'
  have hsum : ∑ y,canonicalMatrix q o y=(q:ℚ)*((q:ℚ)-1)/2 :=
    canonical_zero_row_sum (by omega)
  rw [hsum] at hz
  have hc0 : c=0 := (mul_eq_zero.mp hz).resolve_left hy
  funext y
  exact (hall y).trans hc0

theorem canonical_full_rank {q : ℕ} (hq : 2≤q) : (canonicalMatrix q).rank=q := by
  have hk : LinearMap.ker (canonicalMatrix q).mulVecLin=⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v h
    exact canonical_kernel_zero hq v (LinearMap.mem_ker.mp h)
  rw [Matrix.rank,LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hk),finrank_pi,
    Fintype.card_fin]

theorem dyadic_rank_amplification (m : ℕ) (hm : 0<m) :
    (integerMatrix (2^m)).rank≤2 ∧ (canonicalMatrix (2^m)).rank=2^m := by
  refine ⟨integer_matrix_rank_le_two _,canonical_full_rank ?_⟩
  have h := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 1≤m by omega)
  simpa using h

#print axioms difference_rank_le_two
#print axioms integer_matrix_rank_le_two
#print axioms residueInt_if
#print axioms residueInt_adjacent
#print axioms canonical_adjacent
#print axioms negIndex_involutive
#print axioms canonical_zero_row_sum
#print axioms canonical_kernel_zero
#print axioms canonical_full_rank
#print axioms dyadic_rank_amplification
end Paper5.EscapeE2