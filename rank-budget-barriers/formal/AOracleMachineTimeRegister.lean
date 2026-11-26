import AOracleMachineTimeZero

/-!
# Actual scalar A1 zero-register bit verifier

The compact input here supplies per-vertex tapes and one sparse
per-row coefficient list (independent of the guessed assignments);
there is no lookup indexed by complete row or column assignments.
The zero-mode coefficient is proved directly using constantCoeff.
-/

open scoped BigOperators

namespace AOracleMachineTimeRegister
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul AOracleMachineTimeLocal
open AOracleMachineTimeZero AOracleSuccinct AOracleWitness AOracleThreshold

structure Packed where
  right : List TensorTape
  left : List TensorTape
  rows : List RowTape

def pack {r c m delta : ℕ} (b b' p : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) : Packed :=
  ⟨L.rows.map (packTensor b),L.cols.map (packTensor b'),
    packRows b b' p (List.ofFn (fun j => (j,L.localRecipe j)))⟩

/-- None of the operations in this accepting program use decoded
Nat addresses or arithmetic on unbounded words. -/
def verify (p : ℕ) (G : Packed) (y x d : List Bool) : Meter Bool :=
  let a := runTensors y G.right
  let b := runTensors x G.left
  let v := runRows p y x G.rows
  let q := compareBits d v.result
  ⟨a.result && b.result && q.result,a.steps+b.steps+v.steps+q.steps+4⟩

def localWeight {r c m delta p : ℕ} (L : Recipes (ZMod (2^p)) r c m delta)
    (y : Rows r) (x : Cols c) : ZMod (2^p) :=
  (tensorEval y L.rows*tensorEval x L.cols)*
    ∏ j, LiteralPortCompiler.affine (y j) (linearEval x (L.localRecipe j))

theorem coefficient_zero_exact {r c m delta p : ℕ}
    (L : Recipes (ZMod (2^p)) r c m delta) :
    MvPolynomial.coeff 0 (rootPolynomial (rootTerms L)) =
      ∑ y : Rows r, ∑ x : Cols c, localWeight L y x := by
  change MvPolynomial.constantCoeff (rootPolynomial (rootTerms L)) = _
  simp only [rootPolynomial, map_sum, map_mul, map_prod, MvPolynomial.constantCoeff_C, localWeight]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hn (k : Fin m) : Finsupp.single k (1:ℕ) ≠ 0 := by simp
  cases hy : y j <;> simp [rowPolynomial,LiteralPortCompiler.affine,hy,hn,
    MvPolynomial.constantCoeff_monomial,rootTerms]

theorem verify_exact {r c m delta p : ℕ} (L : Recipes (ZMod (2^p)) r c m delta)
    (y : Rows r) (x : Cols c) (d : Word p) (b b' s : ℕ)
    (hp : 0<p) (hy : r≤2^b) (hx : c≤2^b')
    (hs : ∀ j, (L.localRecipe j).length≤s) :
    let v := verify p (pack b b' p L) (List.ofFn y) (List.ofFn x) (encodeBits p d.val)
    (v.result=true ↔ d.val < (localWeight L y x).val) ∧
      v.steps≤L.rows.length*tensorBudget r delta b+L.cols.length*tensorBudget c delta b'
        +p+r*rowBudget r c b b' p s+10*p+4 := by
  let a := runTensors (List.ofFn y) (L.rows.map (packTensor b))
  let c' := runTensors (List.ofFn x) (L.cols.map (packTensor b'))
  let pRows := List.ofFn (fun j : Fin r => (j,L.localRecipe j))
  let v := runRows p (List.ofFn y) (List.ofFn x) (packRows b b' p pRows)
  obtain ⟨ha,hat⟩ := runTensors_exact y b p hy L.rows
  obtain ⟨hc,hct⟩ := runTensors_exact x b' p hx L.cols
  have hh (t : Fin r × Linear c (ZMod (2^p))) (ht : t ∈ pRows) : t.2.length≤s := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
    exact hs j
  obtain ⟨hl,hv,hvt⟩ := runRows_exact y x b b' p s hp hy hx pRows hh
  change asResidue p v.result = _ at hv
  simp only [pRows,List.map_ofFn,List.prod_ofFn,Function.comp_apply] at hv
  simp only [pRows,List.length_ofFn] at hvt
  have hd := compareBits_exact (encodeBits p d.val) v.result (by rw [encodeBits_length]; exact hl.symm)
  simp only [encodeBits_exact p d.val d.isLt,encodeBits_length] at hd
  have hval : (asResidue p v.result).val=bitsValue v.result := by
    apply ZMod.val_natCast_of_lt
    have hb := bitsValue_lt v.result
    rwa [show v.result.length=p from hl] at hb
  change (if a.result then (1:ZMod (2^p)) else 0)=tensorEval y L.rows at ha
  change (if c'.result then (1:ZMod (2^p)) else 0)=tensorEval x L.cols at hc
  change ((a.result && c'.result && (compareBits (encodeBits p d.val) v.result).result)=true ↔
      d.val < (localWeight L y x).val) ∧
    a.steps+c'.steps+v.steps+(compareBits (encodeBits p d.val) v.result).steps+4 ≤ _
  refine ⟨?_,?_⟩
  · unfold localWeight
    rw [← ha, ← hc, ← hv]
    cases a.result <;> cases c'.result <;> simp [hd.1,hval]
  · change a.steps≤_ at hat
    change c'.steps≤_ at hct
    change v.steps≤_ at hvt
    omega

/-- Count the accepts over the actual three guessed bit words.
The result is the requested genuine algebraic zero coefficient. -/
theorem register_by_bit_machine {r c m delta p : ℕ} (L : Recipes (ZMod (2^p)) r c m delta)
    (b b' s : ℕ) (hp : 0<p) (hy : r≤2^b) (hx : c≤2^b')
    (hs : ∀ j, (L.localRecipe j).length≤s) :
    (countVerify (fun z : (Rows r × Cols c) × Word p =>
      (verify p (pack b b' p L) (List.ofFn z.1.1) (List.ofFn z.1.2)
        (encodeBits p z.2.val)).result) : ZMod (2^p)) =
      MvPolynomial.coeff 0 (rootPolynomial (rootTerms L)) := by
  rw [coefficient_zero_exact]
  have he : (fun z : (Rows r × Cols c) × Word p =>
      (verify p (pack b b' p L) (List.ofFn z.1.1) (List.ofFn z.1.2)
        (encodeBits p z.2.val)).result) =
      verifier (fun w : Rows r × Cols c => some w) (fun _ => true)
        (fun w => localWeight L w.1 w.2) := by
    funext t
    apply Bool.eq_iff_iff.mpr
    change _ ↔ (true && decide (t.2.val<(localWeight L t.1.1 t.1.2).val))=true
    rw [Bool.true_and,decide_eq_true_eq]
    exact (verify_exact L t.1.1 t.1.2 t.2 b b' s hp hy hx hs).1
  rw [he]
  exact total_coordinate_from_count (fun y => tensorEval y L.rows) (fun x => tensorEval x L.cols)
    (fun x j => linearEval x (L.localRecipe j)) (AddMonoidHom.id _)

#print axioms coefficient_zero_exact
#print axioms verify_exact
#print axioms register_by_bit_machine

end AOracleMachineTimeRegister

