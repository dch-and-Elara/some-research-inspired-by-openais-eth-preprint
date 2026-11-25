import AffineCostRecovery
import AffineCostExpr

open Polynomial AffineEdge
open scoped Polynomial BigOperators

namespace AffineCost

variable {q : ℕ} {F : Type*} [Field F]

theorem Expr.eval_ite (sites : Fin q → F) (p : Prop) [Decidable p] (x y : Expr q) :
    Expr.eval sites (if p then x else y) =
      if p then Expr.eval sites x else Expr.eval sites y := by
  split <;> rfl

def wordEqual (u v : Word q) : Bool :=
  (List.finRange q).all fun t => (u.1 t == v.1 t) && (u.2 t == v.2 t)

theorem wordEqual_spec (u v : Word q) : wordEqual u v = true ↔ u = v := by
  simp only [wordEqual, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    beq_iff_eq]
  exact ⟨fun h => Prod.ext (funext fun t => (h t).1) (funext fun t => (h t).2), by
    rintro rfl
    exact fun _ => ⟨rfl,rfl⟩⟩

def parityBits (a : Bits q) : Bool :=
  decide ((List.ofFn (fun t => bitScalar (R := ℕ) (a t))).sum % 2 = 1)

@[simp] theorem parityBits_eq (a : Bits q) : parityBits a = parity a := by
  simp [parityBits, parity, Fin.sum_ofFn]

def scaleExpr (a : Bits q) (t : Fin q) : Expr q × Expr q :=
  let d : Expr q := Expr.sub (.bit (!(a t))) (.bit (a t))
  match partner t with
  | none => (d, .bit false)
  | some s =>
    let a := Expr.mul (.mul d (.site t)) (.inv (Expr.sub (.site t) (.site s)))
    (a, .mul (.site s) a)

def pairExpr (u v : Word q) : Expr q × Expr q :=
  let a := complement u.2
  match scan u u, scan v v with
  | .zero, .zero => (.bit (parityBits v.1 == parityBits a), .bit false)
  | .one t, .one s =>
    let d : Expr q := if bucket s = bucket t then Expr.sub (.bit (v.1 s)) (.bit (a s)) else .bit false
    (.mul (scaleExpr a t).1 d, .mul (scaleExpr a t).2 d)
  | _, _ => (.bit false, .bit false)

theorem scaleExpr_eval (sites : Fin q → F) (a : Bits q) (t : Fin q) :
    ((scaleExpr a t).1.eval sites, (scaleExpr a t).2.eval sites) = scale sites a t := by
  cases h : partner t <;> simp [scaleExpr, scale, h, Expr.eval, Expr.sub, bitDiff, bitScalar,
    sub_eq_add_neg, div_eq_mul_inv]

theorem pairExpr_eval (sites : Fin q → F) (u v : Word q) :
    ((pairExpr u v).1.eval sites, (pairExpr u v).2.eval sites) = coeffPair sites u v := by
  cases hu : scan u u <;> cases hv : scan v v <;>
    simp only [pairExpr, coeffPair, hu, hv, Expr.eval, parityBits_eq, beq_iff_eq,
      Bool.false_eq_true, if_false]
  case one.one t s =>
    have h₀ : (scaleExpr (complement u.2) t).1.eval sites =
        (scale sites (complement u.2) t).1 :=
      congrArg Prod.fst (scaleExpr_eval sites (complement u.2) t)
    have h₁ : (scaleExpr (complement u.2) t).2.eval sites =
        (scale sites (complement u.2) t).2 :=
      congrArg Prod.snd (scaleExpr_eval sites (complement u.2) t)
    rw [h₀,h₁]
    by_cases hb : bucket s = bucket t <;>
      simp only [hb, Bool.false_eq_true, if_true, if_false, Expr.eval, Expr.sub, bitDiff,
        bitScalar, sub_eq_add_neg]

def localExpr (u v : Word q) (i : Fin q) : Expr q :=
  let ab := pairExpr u v
  let r := Expr.sub (.bit (wordEqual u v)) ab.1
  match scan u v with
  | .zero => .bit false
  | .one t => if i = t then r else .bit false
  | .two s t =>
    let l := Expr.mul (Expr.sub (.neg ab.2) (.mul (.site t) r))
      (.inv (Expr.sub (.site s) (.site t)))
    if i = s then l else if i = t then Expr.sub r l else .bit false

theorem localExpr_eval (sites : Fin q → F) (u v : Word q) (i : Fin q) :
    (localExpr u v i).eval sites = localWeight sites u v i := by
  have h₀ : (pairExpr u v).1.eval sites = (coeffPair sites u v).1 :=
    congrArg Prod.fst (pairExpr_eval sites u v)
  have h₁ : (pairExpr u v).2.eval sites = (coeffPair sites u v).2 :=
    congrArg Prod.snd (pairExpr_eval sites u v)
  cases hu : scan u v <;>
    simp only [localExpr,localWeight,hu,Expr.eval_ite,Expr.eval,Expr.sub,
      Bool.false_eq_true,if_false,h₀,h₁,selector,wordEqual_spec,sub_eq_add_neg,div_eq_mul_inv]

def exceptList (t : Fin q) : List (Fin q) :=
  (List.finRange q).filter (fun i => i != t)

theorem exceptList_length (t : Fin q) : (exceptList t).length ≤ q :=
  (List.length_filter_le _ _).trans_eq List.length_finRange

theorem exceptList_toFinset (t : Fin q) : (exceptList t).toFinset = Finset.univ.erase t := by
  ext i
  simp [exceptList, Finset.mem_erase]

/-- The coefficient expression for an output/input entry. All loops range
over explicit finite lists. In particular, there is no search for a solution. -/
def coefficientExpr (u v : Word q) (k : Fin q) : Expr q :=
  let ab := pairExpr u v
  let a := if k.val = 0 then ab.1 else .bit false
  let b := if k.val = q-1 then ab.2 else .bit false
  let n := Expr.inv (.neg (Expr.negLabelProduct (List.finRange q)))
  .add a (.mul n (.add b
    (Expr.sum (List.ofFn fun t => Expr.mul (.mul (.site t) (localExpr u v t))
      (Expr.nodeCoeff (exceptList t) k.val)))))

noncomputable def rowPolynomial (sites : Fin q → F) (u v : Word q) : F[X] :=
  reconstructEntry sites (binaryEncoder q) (fun j => (weights sites u j).1)
    (fun j => (weights sites u j).2) (fun t v => localWeight sites u v t) v

theorem coefficientExpr_eval (sites : Fin q → F) (u v : Word q) (k : Fin q) :
    (coefficientExpr u v k).eval sites = (rowPolynomial sites u v).coeff k.val := by
  classical
  have ha₀ : (pairExpr u v).1.eval sites = (coeffPair sites u v).1 :=
    congrArg Prod.fst (pairExpr_eval sites u v)
  have ha₁ : (pairExpr u v).2.eval sites = (coeffPair sites u v).2 :=
    congrArg Prod.snd (pairExpr_eval sites u v)
  have ht (t : Fin q) :
      (Expr.nodeCoeff (exceptList t) k.val).eval sites =
        (∏ s ∈ Finset.univ.erase t, (X - Polynomial.C (sites s))).coeff k.val := by
    have hd : (exceptList t).Nodup := (List.nodup_finRange q).filter _
    rw [Expr.eval_nodeCoeff, ← List.prod_toFinset _ hd,
      exceptList_toFinset]
  change _ = (Polynomial.C (∑ j : EncoderRow q, (weights sites u j).1 * binaryEncoder q j v) +
    Polynomial.C ((-(∏ t, -sites t))⁻¹) *
    (Polynomial.C (∑ j : EncoderRow q, (weights sites u j).2 * binaryEncoder q j v) * X^(q-1) +
    ∑ t, Polynomial.C (sites t * localWeight sites u v t) *
      ∏ s ∈ Finset.univ.erase t, (X - Polynomial.C (sites s)))).coeff k.val
  have hf (t : Fin q) :
      (Expr.mul (.mul (.site t) (localExpr u v t)) (Expr.nodeCoeff (exceptList t) k.val)).eval sites =
        sites t * localWeight sites u v t *
          (∏ s ∈ Finset.univ.erase t, (X - Polynomial.C (sites s))).coeff k.val := by
    simp only [Expr.eval, localExpr_eval, ht]
  have hsum :
      (Expr.sum (List.ofFn fun t : Fin q => Expr.mul (.mul (.site t) (localExpr u v t))
        (Expr.nodeCoeff (exceptList t) k.val))).eval sites =
      ∑ t, sites t * localWeight sites u v t *
        (∏ s ∈ Finset.univ.erase t, (X - Polynomial.C (sites s))).coeff k.val := by
    rw [Expr.eval_sum, List.map_ofFn, Fin.sum_ofFn]
    exact Finset.sum_congr rfl fun t _ => hf t
  have hprod : ((List.finRange q).map (fun t => -sites t)).prod = ∏ t, -sites t := by
    rw [← List.ofFn_eq_map, Fin.prod_ofFn]
  simp only [coefficientExpr, Expr.eval, hsum, Expr.eval_negLabelProduct, hprod,
    coeff_add, coeff_C_mul, finset_sum_coeff, coeff_X_pow,
    (weights_sum sites u v).1, (weights_sum sites u v).2]
  simp only [Expr.eval_ite, Expr.eval, ha₀, ha₁, Bool.false_eq_true, if_false, coeff_C,
    mul_ite, mul_one, mul_zero]

theorem rowPolynomial_correct (sites : Fin q → F) (hq : 2 ≤ q)
    (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0) :
    PairedCondition sites (binaryEncoder q) (q-2) (rowPolynomial sites) :=
  reconstruct_matrix_of_rowSystems hq hn (explicit_rowSystem sites hi)

private theorem scaleExpr_nodes (a : Bits q) (t : Fin q) :
    (scaleExpr a t).1.nodes ≤ 20 ∧ (scaleExpr a t).2.nodes ≤ 20 := by
  cases h : partner t <;> simp [scaleExpr, h, Expr.nodes, Expr.sub]

theorem pairExpr_nodes (u v : Word q) :
    (pairExpr u v).1.nodes ≤ 26 ∧ (pairExpr u v).2.nodes ≤ 26 := by
  cases hu : scan u u <;> cases hv : scan v v <;>
    simp [pairExpr, hu, hv, Expr.nodes]
  case one.one t s =>
    have h := scaleExpr_nodes (complement u.2) t
    split <;> simp [Expr.sub, Expr.nodes] <;> omega

theorem localExpr_nodes (u v : Word q) (i : Fin q) :
    (localExpr u v i).nodes ≤ 160 := by
  have h := pairExpr_nodes u v
  cases hu : scan u v with
  | zero => simp [localExpr, hu, Expr.nodes]
  | one t => by_cases he : i = t <;> simp [localExpr, hu, he, Expr.nodes, Expr.sub] <;> omega
  | two s t =>
    simp only [localExpr,hu]
    split
    · simp [Expr.nodes, Expr.sub]; omega
    · split <;> simp [Expr.nodes, Expr.sub] <;> omega

theorem coefficientExpr_nodes (u v : Word q) (k : Fin q) :
    (coefficientExpr u v k).nodes ≤ 1024*(q+1)*2^q := by
  have hp := pairExpr_nodes u v
  have hn (t : Fin q) : (Expr.nodeCoeff (exceptList t) k.val).nodes ≤ 5*2^q :=
    (show (Expr.nodeCoeff (exceptList t) k.val).nodes ≤ 5*2^(exceptList t).length by
      have := Expr.nodeCoeff_nodes (exceptList t) k.val
      omega).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (exceptList_length t)))
  have hs := Expr.sum_nodes (List.ofFn fun t => Expr.mul (.mul (.site t) (localExpr u v t))
      (Expr.nodeCoeff (exceptList t) k.val)) (166+5*2^q) (by
    intro x hx
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hx
    have := localExpr_nodes u v t
    have := hn t
    simp only [Expr.nodes]
    omega)
  simp only [coefficientExpr, Expr.nodes, Expr.negLabelProduct_nodes, List.length_finRange,
    List.length_ofFn] at *
  have hpow : 1 ≤ 2^q := Nat.pow_pos (by decide)
  have hm : 1*q ≤ 2^q*q := Nat.mul_le_mul_right _ hpow
  split <;> split <;> (try simp only [Expr.nodes]) <;> nlinarith

end AffineCost
