import A1R9Register

/-! Remove free abstract parsing from the scalar bit-machine count.
Malformed option fields are detected by a metered Boolean tape pass
before any coefficient or moment is read. The accepted witness path
then uses the frozen row/multiplicity routines unchanged. -/

namespace A1R9
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeLocal
open AOracleMachineTimeZero AOracleSuccinct AOracleWitness AOracleThreshold

theorem append_zero_value (xs : List Bool) : bitsValue (xs++[false])=bitsValue xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [bitsValue,ih]

def checkFrames (limit : List Bool) : List (List Bool) → Meter Bool
  | [] => ⟨true,0⟩
  | a::as =>
    let h := compareBits (a++[false]) limit
    let t := checkFrames limit as
    ⟨h.result && t.result,h.steps+t.steps+2*limit.length+4⟩

theorem checkFrames_exact (limit : List Bool) (xs : List (List Bool))
    (width : ∀ a∈xs,a.length+1=limit.length) :
    ((checkFrames limit xs).result=true ↔ ∀ a∈xs, bitsValue a<bitsValue limit) ∧
    (checkFrames limit xs).steps=xs.length*(12*limit.length+4) := by
  induction xs with
  | nil => simp [checkFrames]
  | cons a as ih =>
    have hlen : (a++[false]).length=limit.length := by simpa using width a List.mem_cons_self
    obtain ⟨ha,ht⟩ := compareBits_exact (a++[false]) limit hlen
    obtain ⟨hb,hbt⟩ := ih (fun x hx => width x (List.mem_cons_of_mem _ hx))
    simp only [append_zero_value] at ha
    constructor
    · simp [checkFrames,ha,hb]
    · change (compareBits (a++[false]) limit).steps+(checkFrames limit as).steps+
        2*limit.length+4=(as.length+1)*(12*limit.length+4)
      rw [ht,hbt,hlen,Nat.succ_mul as.length (12*limit.length+4)]
      omega

def rawChoices {r c b : ℕ} (z : Code r c b) : List (List Bool) :=
  List.ofFn (fun j => encodeBits b (z.2.2 j).val)

def frameCode {r c b : ℕ} (m : ℕ) (z : Code r c b) : Meter Bool :=
  checkFrames (encodeBits (b+1) (m+1)) (rawChoices z)

theorem frameCode_exact {r c b : ℕ} (m : ℕ) (fit : m+1≤2^b)
    (z : Code r c b) :
    ((frameCode m z).result=true ↔ ∀ j, (z.2.2 j).val<m+1) ∧
    (frameCode m z).steps=r*(12*(b+1)+4) := by
  have hfit : m+1<2^(b+1) := by
    rw [pow_succ]
    have h : 0 < (2:ℕ)^b := by positivity
    omega
  obtain ⟨he,ht⟩ := checkFrames_exact (encodeBits (b+1) (m+1)) (rawChoices z) (by
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    rw [encodeBits_length,encodeBits_length])
  refine ⟨?_,?_⟩
  · change (checkFrames (encodeBits (b+1) (m+1)) (rawChoices z)).result=true ↔ _
    rw [he,encodeBits_exact _ _ hfit]
    constructor
    · intro h j
      have hj := h (encodeBits b (z.2.2 j).val) (List.mem_ofFn.mpr ⟨j,rfl⟩)
      rwa [encodeBits_exact b _ (z.2.2 j).isLt] at hj
    · intro h a ha
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
      rw [encodeBits_exact b _ (z.2.2 j).isLt]
      exact h j
  · change (checkFrames (encodeBits (b+1) (m+1)) (rawChoices z)).steps=_
    rw [ht,encodeBits_length]
    simp [rawChoices]

def runRawScalar {r c m delta p : ℕ} (br bc bm bq : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) (beta : Fin m →₀ ℕ)
    (y x : List Bool) (alloc : List (List Bool)) (d : List Bool) : Meter Bool :=
  let a := runTensors y (L.rows.map (packTensor br))
  let b := runTensors x (L.cols.map (packTensor bc))
  let rows := runSelected p x y alloc (List.ofFn (pickTape bc L))
  let count := checkMultiplicity bm bq beta alloc
  let out := compareBits d rows.result.2
  ⟨a.result && b.result && rows.result.1 && count.result && out.result,
    a.steps+b.steps+rows.steps+count.steps+out.steps+8⟩

def scalarBitMachine {r c m delta p : ℕ} (br bc bm bq : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) (beta : Fin m →₀ ℕ)
    (code : Code r c bm × Word p) : Meter Bool :=
  let f := frameCode m code.1
  if f.result then
    let v := runRawScalar br bc bm bq L beta (List.ofFn code.1.1) (List.ofFn code.1.2.1)
      (rawChoices code.1) (encodeBits p code.2.val)
    ⟨v.result,f.steps+v.steps+2⟩
  else ⟨false,f.steps+2⟩

theorem scalarBitMachine_model {r c m delta p : ℕ} (br bc bm bq s : ℕ)
    (hp : 0<p) (hq : 0<bq) (hr : r≤2^br) (hc : c≤2^bc) (hm : m+1≤2^bm) (hrq : r<2^bq)
    (L : Recipes (ZMod (2^p)) r c m delta) (beta : Fin m →₀ ℕ)
    (hb : ∀ k, beta k<2^bq) (hL : ∀ j, (L.localRecipe j).length≤s)
    (hM : ∀ k, (L.moment k).length≤s) (code : Code r c bm × Word p) :
    let v := scalarBitMachine br bc bm bq L beta code
    v.result=scalarVerifyCode br bc bm bq L beta code ∧
      v.steps≤r*(12*(bm+1)+4)+witnessBudget br bc bm bq s L+2 := by
  let f := frameCode m code.1
  obtain ⟨hre,hrt⟩ := frameCode_exact m hm code.1
  change (f.result=true ↔ _) at hre
  change f.steps=_ at hrt
  unfold scalarBitMachine scalarVerifyCode
  dsimp only
  change _ ∧ (if f.result then _ else _ : Meter Bool).steps≤_
  cases hh : parse code.1 with
  | none =>
    have hbad : f.result=false := by
      apply Bool.eq_false_iff.mpr
      intro hs
      have hg := hre.1 hs
      simp [parse,hg] at hh
    simp [hbad,hrt,f]
  | some w =>
    have hz : code.1=encode hm w := (parse_exact hm _ _).1 hh
    have hf : f.result=true := hre.2 (by rw [hz]; exact fun j => (w.2.2 j).isLt)
    rw [if_pos hf,Option.elim_some]
    have ht : runRawScalar br bc bm bq L beta (List.ofFn code.1.1) (List.ofFn code.1.2.1)
          (rawChoices code.1) (encodeBits p code.2.val) =
        scalarVerify br bc bm bq L beta w code.2 := by
      rw [hz]
      rfl
    rw [ht,hrt]
    have h := (scalarVerify_exact br bc bm bq s hp hq hr hc hm hrq L beta hb hL hM w code.2).2
    refine ⟨rfl,?_⟩
    dsimp only at h ⊢
    omega

theorem scalarBitMachine_count {r c m delta p : ℕ} (br bc bm bq s : ℕ)
    (hp : 0<p) (hq : 0<bq) (hr : r≤2^br) (hc : c≤2^bc) (hm : m+1≤2^bm) (hrq : r<2^bq)
    (L : Recipes (ZMod (2^p)) r c m delta) (beta : Fin m →₀ ℕ)
    (hb : ∀ k, beta k<2^bq) (hL : ∀ j, (L.localRecipe j).length≤s)
    (hM : ∀ k, (L.moment k).length≤s) :
    (countVerify (fun code => (scalarBitMachine br bc bm bq L beta code).result) : ZMod (2^p)) =
      MvPolynomial.coeff beta (rootPolynomial (rootTerms L)) := by
  have h : (fun code => (scalarBitMachine br bc bm bq L beta code).result) =
      scalarVerifyCode br bc bm bq L beta := by
    funext code
    exact (scalarBitMachine_model br bc bm bq s hp hq hr hc hm hrq L beta hb hL hM code).1
  rw [h]
  exact scalarRegister_by_count br bc bm bq s hp hq hr hc hm hrq L beta hb hL hM

#print axioms checkFrames_exact
#print axioms frameCode_exact
#print axioms scalarBitMachine_model
#print axioms scalarBitMachine_count
end A1R9
