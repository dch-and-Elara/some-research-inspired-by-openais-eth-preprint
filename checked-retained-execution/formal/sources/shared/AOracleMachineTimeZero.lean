import AOracleMachineTimeLocal

/-!
# End-to-end bit program for the scalar zero mode

For a prescribed scalar zero-mode register the only guessed fields
are the independent Boolean port tapes and a p-bit threshold. Original
vertices are evaluated by local scans, and each original row reads
just one sparse local recipe. No total-assignment-indexed tables are
given to the verifier. General extension/mode decoding is separate.
-/

open scoped BigOperators

namespace AOracleMachineTimeZero
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul AOracleMachineTimeLocal
open AOracleSuccinct AOracleWitness AOracleThreshold

theorem complement_integer (a : List Bool) :
    bitsValue a + bitsValue (a.map not)+1=2^a.length := by
  induction a with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [List.map_cons, bitsValue, List.length_cons, pow_succ,
      Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem complement_ring (p : ℕ) (a : List Bool) (hl : a.length=p) :
    asResidue p (a.map not)+1=-asResidue p a := by
  have h := congrArg (fun n : ℕ => (n:ZMod (2^p))) (complement_integer a)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, hl, ring_nilpotent] at h
  unfold asResidue
  apply eq_neg_of_add_eq_zero_left
  linear_combination h

/-- Actual ripple computation of 1-x, useful for the affine l_0.
A seed carry is not needed: x̄+2 implements 1-x mod 2^p. -/
def oneSub (p : ℕ) (a : List Bool) : Meter (List Bool) :=
  let r := addBits (a.map not) (encodeBits p 2)
  ⟨r.result,r.steps+3*p⟩

theorem encode_two (p : ℕ) (hp : 0<p) :
    asResidue p (encodeBits p 2)=(2:ZMod (2^p)) := by
  cases p with
  | zero => omega
  | succ p =>
    cases p with
    | zero => decide
    | succ p =>
      unfold asResidue
      rw [encodeBits_exact]
      · rfl
      · rw [pow_succ, pow_succ]
        have : 0 < (2:ℕ)^p := by positivity
        omega

theorem oneSub_exact (p : ℕ) (hp : 0<p) (a : List Bool) (hl : a.length=p) :
    (oneSub p a).result.length=p ∧
      asResidue p (oneSub p a).result=1-asResidue p a ∧
      (oneSub p a).steps=15*p := by
  have hleft : (a.map not).length=p := by simpa using hl
  have hright := encodeBits_length p 2
  have h := addBits_exact (a.map not) (encodeBits p 2) (hleft.trans hright.symm)
  refine ⟨h.1.trans hleft,?_,?_⟩
  · change asResidue p (addBits (a.map not) (encodeBits p 2)).result=_
    rw [add_residue p _ _ hleft hright, encode_two p hp]
    linear_combination complement_ring p a hl
  · change (addBits (a.map not) (encodeBits p 2)).steps+3*p=15*p
    rw [h.2.2,hleft]
    omega

abbrev TensorTape := List (List Bool) × List Bool

def packTensor {n delta : ℕ} (b : ℕ) (T : BoolTensor n delta) : TensorTape :=
  (((List.ofFn T.port).map (fun j => encodeBits b j.val)),List.ofFn T.table)

def runTensors (as : List Bool) : List TensorTape → Meter Bool
  | [] => ⟨true,0⟩
  | t :: ts =>
    let h := readTensor t.1 t.2 as
    let z := runTensors as ts
    ⟨h.result && z.result,h.steps+z.steps+2⟩

def tensorBudget (n delta b : ℕ) : ℕ :=
  delta*((10*b+4)*n+2)+(10*delta+4)*2^delta+4

theorem runTensors_exact {n delta : ℕ} (a : Fin n → Bool) (b p : ℕ)
    (hfit : n≤2^b) (ts : List (BoolTensor n delta)) :
    let v := runTensors (List.ofFn a) (ts.map (packTensor b))
    (if v.result then (1:ZMod (2^p)) else 0)=tensorEval a ts ∧
      v.steps≤ts.length*tensorBudget n delta b := by
  induction ts with
  | nil => simp [runTensors, tensorEval]
  | cons T ts ih =>
    obtain ⟨hsem,hcost⟩ := ih
    obtain ⟨htrue,htime⟩ := readTensor_exact T a b hfit
    change ((if ((readTensor (packTensor b T).1 (packTensor b T).2 (List.ofFn a)).result &&
      (runTensors (List.ofFn a) (ts.map (packTensor b))).result) then (1:ZMod (2^p)) else 0)
      = tensorEval a (T::ts)) ∧ _
    rw [show (readTensor (packTensor b T).1 (packTensor b T).2 (List.ofFn a)).result =
      T.read a from htrue]
    constructor
    · rw [tensorEval,← hsem]
      cases T.read a <;> simp
    · have ha : T.arity*((10*b+4)*n+2)≤delta*((10*b+4)*n+2) :=
        Nat.mul_le_mul_right _ T.small
      have hb : (10*T.arity+4)*2^T.arity≤(10*delta+4)*2^delta :=
        Nat.mul_le_mul (by have := T.small; omega) (Nat.pow_le_pow_right (by decide) T.small)
      change (readTensor (packTensor b T).1 (packTensor b T).2 (List.ofFn a)).steps+
        (runTensors (List.ofFn a) (ts.map (packTensor b))).steps+2 ≤
          (ts.length+1)*tensorBudget n delta b
      have hT : (readTensor (packTensor b T).1 (packTensor b T).2 (List.ofFn a)).steps+2 ≤
          tensorBudget n delta b := by
        change (readTensor (packTensor b T).1 (packTensor b T).2 (List.ofFn a)).steps≤_ at htime
        unfold tensorBudget
        omega
      rw [Nat.add_mul,one_mul]
      omega

abbrev RowTape := List Bool × List (List Bool × List Bool)

def runRows (p : ℕ) (y x : List Bool) : List RowTape → Meter (List Bool)
  | [] => ⟨encodeBits p 1,p⟩
  | t :: ts =>
    let bit := seek t.1 y
    let z := runLinear p x t.2
    let a := if bit.result.getD false then Meter.pure z.result else oneSub p z.result
    let rest := runRows p y x ts
    let out := multiply a.result rest.result
    ⟨out.result,bit.steps+z.steps+a.steps+rest.steps+out.steps+6⟩

def packRows {r c : ℕ} (b b' p : ℕ)
    (xs : List (Fin r × Linear c (ZMod (2^p)))) : List RowTape :=
  xs.map (fun jl => (encodeBits b jl.1.val,packLinear b' p jl.2))

def rowBudget (r c b b' p s : ℕ) : ℕ :=
  (10*b+4)*r + p+s*((10*b'+4)*c+12*p+4)+15*p+16*(p+1)^2+6

theorem runRows_exact {r c : ℕ} (y : Fin r → Bool) (x : Fin c → Bool)
    (b b' p s : ℕ) (hp : 0<p) (hy : r≤2^b) (hx : c≤2^b')
    (ls : List (Fin r × Linear c (ZMod (2^p))))
    (hs : ∀ t ∈ ls, t.2.length≤s) :
    let v := runRows p (List.ofFn y) (List.ofFn x) (packRows b b' p ls)
    v.result.length=p ∧ asResidue p v.result =
        (ls.map (fun t => LiteralPortCompiler.affine (y t.1) (linearEval x t.2))).prod ∧
      v.steps≤p+ls.length*rowBudget r c b b' p s := by
  induction ls with
  | nil =>
    have h : 1<(2:ℕ)^p := one_lt_pow₀ (by decide) hp.ne'
    simp [runRows,packRows,encodeBits_length,asResidue,encodeBits_exact p 1 h]
  | cons t ls ih =>
    rcases t with ⟨j,l⟩
    obtain ⟨hlen,hsem,hcost⟩ := ih (fun t ht => hs t (List.mem_cons_of_mem _ ht))
    have hls := hs (j,l) (List.mem_cons_self)
    obtain ⟨hseek,hts⟩ := encoded_seek b j.val (j.isLt.trans_le hy) (List.ofFn y)
    have hb : (seek (encodeBits b j.val) (List.ofFn y)).result=some (y j) := by
      rw [hseek]
      simp [j.isLt]
    rw [List.length_ofFn] at hts
    obtain ⟨hlin,hval,hcl⟩ := runLinear_exact x b' p l hx
    have hlc := Nat.mul_le_mul_right ((10*b'+4)*c+12*p+4) hls
    let base := runLinear p (List.ofFn x) (packLinear b' p l)
    let adj := if (y j) then Meter.pure base.result else oneSub p base.result
    change asResidue p base.result=linearEval x l at hval
    change base.steps≤_ at hcl
    change l.length*((10*b'+4)*c+12*p+4)≤_ at hlc
    have ha : adj.result.length=p ∧
        asResidue p adj.result=LiteralPortCompiler.affine (y j) (linearEval x l) ∧
        adj.steps≤15*p := by
      cases hh : y j
      · obtain ⟨hh1,hh2,hh3⟩ := oneSub_exact p hp base.result hlin
        rw [hval] at hh2
        simpa [adj,hh,LiteralPortCompiler.affine] using
          (show _ ∧ _ ∧ (oneSub p base.result).steps≤15*p from ⟨hh1,hh2,hh3.le⟩)
      · exact ⟨by simpa [adj,hh,Meter.pure] using hlin,
          by simpa [adj,hh,Meter.pure,LiteralPortCompiler.affine] using hval,
          by simp [adj,hh,Meter.pure]⟩
    have hmul := multiply_result p adj.result
      (runRows p (List.ofFn y) (List.ofFn x) (packRows b b' p ls)).result ha.1
    have hcm := square_word_cost p adj.result
      (runRows p (List.ofFn y) (List.ofFn x) (packRows b b' p ls)).result ha.1 hlen
    rw [show packRows b b' p ((j,l)::ls) =
      (encodeBits b j.val,packLinear b' p l)::packRows b b' p ls by rfl, runRows]
    dsimp only
    rw [hb]
    change _ ∧ asResidue p (multiply adj.result
      (runRows p (List.ofFn y) (List.ofFn x) (packRows b b' p ls)).result).result = _ ∧ _
    refine ⟨hmul.1, ?_, ?_⟩
    · rw [hmul.2.1,ha.2.1,hsem]
      rfl
    · have hcur : (seek (encodeBits b j.val) (List.ofFn y)).steps+base.steps+adj.steps+
          (multiply adj.result (runRows p (List.ofFn y) (List.ofFn x)
            (packRows b b' p ls)).result).steps+6 ≤ rowBudget r c b b' p s := by
        unfold rowBudget
        have hadj := ha.2.2
        omega
      change (seek (encodeBits b j.val) (List.ofFn y)).steps+base.steps+adj.steps+
        (runRows p (List.ofFn y) (List.ofFn x) (packRows b b' p ls)).steps+
        (multiply adj.result (runRows p (List.ofFn y) (List.ofFn x)
          (packRows b b' p ls)).result).steps+6 ≤ p+(ls.length+1)*rowBudget r c b b' p s
      rw [Nat.add_mul,one_mul]
      omega

#print axioms oneSub_exact
#print axioms runTensors_exact
#print axioms runRows_exact

end AOracleMachineTimeZero

