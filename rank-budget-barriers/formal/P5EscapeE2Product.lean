import RBBoolean
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! The exact compact product in Paper 5 §9 and its one-source,
input-dependent fan-out implementation. Arithmetical gate counts below
are not confused with a unit-cost charge for arbitrary-size integers. -/
namespace Paper5.EscapeE2
open scoped BigOperators
open Matrix

abbrev Bits (m : ℕ) := Fin m→Bool

def bit (x : Bool) : ℚ := if x then 1 else 0

def chosenBits {m : ℕ} (x : Bits m) : Finset (Fin m) :=
  Finset.univ.filter fun i=>x i=true

def bitSubsetEquiv (m : ℕ) : Bits m ≃ Finset (Fin m) where
  toFun := chosenBits
  invFun S i := decide (i∈S)
  left_inv x := by
    funext i
    cases h : x i <;> simp [chosenBits,h]
  right_inv S := by ext i; simp [chosenBits]

def monomial {m : ℕ} (S : Finset (Fin m)) (x : Bits m) : ℚ :=
  ∏ i∈S, bit (x i)

def compactProduct {m : ℕ} (x y : Bits m) : ℚ :=
  ∏ i : Fin m, (1+bit (x i)*bit (y i))

def productMatrix (m : ℕ) : Matrix (Bits m) (Bits m) ℚ :=
  Matrix.of fun x y=>compactProduct x y

theorem compact_expansion {m : ℕ} (x y : Bits m) :
    compactProduct x y=∑ S : Finset (Fin m),monomial S x*monomial S y := by
  simpa [compactProduct,monomial,Finset.prod_mul_distrib] using
    (Finset.prod_one_add (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => bit (x i)*bit (y i)))

theorem compact_geometric_value {m : ℕ} (x y : Bits m) :
    compactProduct x y=(2:ℚ)^(chosenBits x∩chosenBits y).card := by
  have H (i : Fin m) : 1+bit (x i)*bit (y i) =
      if i∈chosenBits x∩chosenBits y then (2:ℚ) else 1 := by
    cases hx : x i <;> cases hy : y i <;> norm_num [chosenBits,bit,hx,hy]
  unfold compactProduct
  simp_rw [H]
  rw [←Finset.prod_filter]
  have hh : (Finset.univ.filter (fun i=>i∈chosenBits x∩chosenBits y))=chosenBits x∩chosenBits y := by
    ext i; simp
  rw [hh,Finset.prod_const]

theorem compact_product_rank (m : ℕ) : (productMatrix m).rank=2^m := by
  classical
  let E := bitSubsetEquiv m
  have h : Matrix.reindex E E (productMatrix m) =
      Matrix.of fun A B : Finset (Fin m)=>(1-(-1:ℚ))^(A∩B).card := by
    ext A B
    change compactProduct (E.symm A) (E.symm B)=_
    rw [compact_geometric_value]
    change (2:ℚ)^(E (E.symm A)∩E (E.symm B)).card=_
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    norm_num
  rw [←Matrix.rank_reindex E E,h]
  simpa using (RankBudget.cubeFullRank (α:=Fin m) (-1:ℚ) (by norm_num))

theorem monomial_is_zeta {m : ℕ} (S : Finset (Fin m)) (x : Bits m) :
    monomial S x=RankBudget.boolZeta ℚ (chosenBits x) S := by
  classical
  unfold RankBudget.boolZeta monomial
  split_ifs with H
  · apply Finset.prod_eq_one
    intro i hi
    have h : x i=true := by simpa [chosenBits] using H hi
    simp [bit,h]
  · obtain ⟨i,hi,hn⟩ := Finset.not_subset.mp H
    refine Finset.prod_eq_zero hi ?_
    have h : x i=false := by simpa [chosenBits] using hn
    simp [bit,h]

theorem independent_monomials (m : ℕ) :
    LinearIndependent ℚ (fun S : Finset (Fin m) => (monomial S : Bits m→ℚ)) := by
  classical
  let Z : Matrix (Finset (Fin m)) (Finset (Fin m)) ℚ := Matrix.of (RankBudget.boolZeta ℚ)
  have hz : IsUnit Z := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    change IsUnit (Matrix.of (RankBudget.boolZeta (α:=Fin m) ℚ)).det
    rw [RankBudget.boolZeta_det]; exact isUnit_one)
  have hf : LinearIndependent ℚ Z.col := Matrix.linearIndependent_cols_iff_isUnit.mpr hz
  let L : (Finset (Fin m)→ℚ) →ₗ[ℚ] (Bits m→ℚ) :=
    LinearMap.funLeft ℚ ℚ (bitSubsetEquiv m)
  have hL : Function.Injective L := by
    intro x y h
    funext S
    obtain ⟨u,hu⟩ := (bitSubsetEquiv m).surjective S
    have hh := congrFun h u
    change x (bitSubsetEquiv m u)=y (bitSubsetEquiv m u) at hh
    rwa [hu] at hh
  convert hf.map' L ((LinearMap.ker_eq_bot).mpr hL) using 1
  funext S x
  exact monomial_is_zeta S x

def pairWeight (m : ℕ) (i : Fin m) : Matrix (Bits m) (Bits m) ℚ :=
  Matrix.vecMulVec (fun x=>bit (x i)) (fun y=>bit (y i))

theorem pair_weight_rank_le_one (m : ℕ) (i : Fin m) : (pairWeight m i).rank≤1 :=
  Matrix.rank_vecMulVec_le _ _

theorem pair_weight_rank_one (m : ℕ) (i : Fin m) : (pairWeight m i).rank=1 := by
  classical
  have h := pair_weight_rank_le_one m i
  refine Nat.le_antisymm h ?_
  by_contra! hzero
  have he : Module.finrank ℚ (LinearMap.range (pairWeight m i).mulVecLin)=0 := by
    change (pairWeight m i).rank=0
    omega
  have hbot : LinearMap.range (pairWeight m i).mulVecLin=⊥ :=
    Submodule.finrank_eq_zero.mp he
  let u : Bits m := fun _=>true
  let a : Bits m→ℚ := fun x=>if x=u then 1 else 0
  have hv := LinearMap.mem_range_self (pairWeight m i).mulVecLin a
  rw [hbot,Submodule.mem_bot] at hv
  have hh : (∑ x : Bits m,pairWeight m i u x*a x)=0 := congrFun hv u
  simp [pairWeight,Matrix.vecMulVec_apply,a,mul_ite,u,bit] at hh

/-- Evaluate a formula with one integer pair product, one addition, and
one multiply into the running product per pair. -/
def productRun : List (Bool×Bool) → ℕ×ℕ
  | [] => (1,0)
  | xy::tail =>
    let r := productRun tail
    let p := xy.1.toNat*xy.2.toNat
    ((1+p)*r.1,r.2+3)

theorem product_run_value (l : List (Bool×Bool)) :
    (productRun l).1=(l.map fun xy=>1+xy.1.toNat*xy.2.toNat).prod := by
  induction l with
  | nil => rfl
  | cons xy l ih => simp [productRun,ih]

theorem product_run_count (l : List (Bool×Bool)) : (productRun l).2=3*l.length := by
  induction l with
  | nil => rfl
  | cons xy l ih =>
    simp only [productRun,ih,List.length_cons,Nat.mul_succ]

theorem product_run_value_width (l : List (Bool×Bool)) :
    (productRun l).1≤2^l.length ∧ (productRun l).1<2^(l.length+1) := by
  have hg : (productRun l).1≤2^l.length := by
    induction l with
    | nil => decide
    | cons xy l ih =>
      have h : 1+xy.1.toNat*xy.2.toNat≤2 := by
        rcases xy with ⟨a,b⟩
        cases a <;> cases b <;> decide
      simp only [productRun,List.length_cons,pow_succ]
      simpa [Nat.mul_comm] using Nat.mul_le_mul h ih
  refine ⟨hg,hg.trans_lt ?_⟩
  exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem literal_product_run {m : ℕ} (x y : Bits m) :
    ((productRun (List.ofFn fun i=>(x i,y i))).1:ℚ)=compactProduct x y ∧
    (productRun (List.ofFn fun i=>(x i,y i))).2=3*m ∧
    (productRun (List.ofFn fun i=>(x i,y i))).1<2^(m+1) := by
  refine ⟨?_,by simp [product_run_count],
    by simpa using (product_run_value_width (List.ofFn fun i : Fin m=>(x i,y i))).2⟩
  rw [product_run_value,List.map_ofFn,List.prod_ofFn]
  push_cast
  unfold compactProduct
  apply Finset.prod_congr rfl
  intro i _
  cases hx : x i <;> cases hy : y i <;> norm_num [bit,hx,hy]

def sourceFanOut : List (Bool×Bool) → ℕ
  | [] => 1
  | xy::tail =>
    let z := sourceFanOut tail
    z+xy.1.toNat*xy.2.toNat*z

theorem single_source_collected_transfer (l : List (Bool×Bool)) :
    sourceFanOut l=(productRun l).1 := by
  induction l with
  | nil => rfl
  | cons xy l ih =>
    simp only [sourceFanOut,productRun,ih]
    ring

/-- The left-to-right fan-out run really uses the same cached value
on both incoming paths and processes the input pairs in their given order. -/
def fanRun (z : ℕ) : List (Bool×Bool)→ℕ×ℕ
  | [] => (z,0)
  | xy::tail =>
    let w := xy.1.toNat*xy.2.toNat
    let p := fanRun (z+w*z) tail
    (p.1,p.2+3)

theorem fan_run_value_and_gates (l : List (Bool×Bool)) (z : ℕ) :
    fanRun z l=(z*(productRun l).1,3*l.length) := by
  induction l generalizing z with
  | nil => simp [fanRun,productRun]
  | cons xy l ih =>
    simp only [fanRun,ih,productRun,List.length_cons,Nat.mul_succ]
    congr 1
    ring

def fanMatrix (m : ℕ) : Matrix (Bits m) (Bits m) ℚ :=
  Matrix.of fun x y => ((fanRun 1 (List.ofFn fun i=>(x i,y i))).1:ℚ)

theorem fan_full_rank_and_cost (m : ℕ) :
    (fanMatrix m).rank=2^m ∧
      ∀ x y : Bits m, (fanRun 1 (List.ofFn fun i=>(x i,y i))).2=3*m := by
  have h : fanMatrix m=productMatrix m := by
    ext x y
    change ((fanRun 1 (List.ofFn fun i=>(x i,y i))).1:ℚ)=compactProduct x y
    rw [fan_run_value_and_gates,one_mul]
    exact (literal_product_run x y).1
  refine ⟨by rw [h]; exact compact_product_rank m,?_⟩
  intro x y
  rw [fan_run_value_and_gates,List.length_ofFn]

#print axioms compact_expansion
#print axioms compact_geometric_value
#print axioms compact_product_rank
#print axioms monomial_is_zeta
#print axioms independent_monomials
#print axioms pair_weight_rank_le_one
#print axioms pair_weight_rank_one
#print axioms product_run_value
#print axioms product_run_count
#print axioms product_run_value_width
#print axioms literal_product_run
#print axioms single_source_collected_transfer
#print axioms fan_run_value_and_gates
#print axioms fan_full_rank_and_cost
end Paper5.EscapeE2