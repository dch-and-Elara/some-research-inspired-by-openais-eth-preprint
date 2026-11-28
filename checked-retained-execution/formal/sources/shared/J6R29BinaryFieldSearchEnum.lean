
import J6R27PrescribedProbeBits

/-! Enumerate the literal binary tails of every requested degree. The
tape generator visits the original 2^d monic possibilities, starting
with the all-zero lower tail. Divisors are materialized degree by degree. -/
namespace J6R29BinaryFieldSearch
open A1R10 AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open J6R27PrescribedProbe
set_option maxHeartbeats 4500000

theorem equal_width_inj (xs ys : List Bool)
    (width : xs.length=ys.length) (val : bitsValue xs=bitsValue ys) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b ys => simp at width
  | cons a xs ih =>
    cases ys with
    | nil => simp at width
    | cons b ys =>
      have H : a=b := by
        cases a <;> cases b <;> simp [bitsValue] at val ⊢ <;> omega
      subst b
      have V : bitsValue xs=bitsValue ys := by
        cases a <;> simp [bitsValue] at val <;> omega
      exact congrArg (List.cons a) (ih ys (Nat.succ.inj width) V)

def candidateWords (e : ℕ) : Meter (List (Word e)) :=
  let R := positiveTape e (2^e-1)
  ⟨wordZero e::R.result,R.steps+4*e+5⟩

def candidateFee (e : ℕ) : ℕ :=
  positiveTapeFee e (2^e-1)+4*e+5

theorem candidate_words_exact (e : ℕ) (he : 0<e) :
    (candidateWords e).result.length=2^e ∧
    (∀ x : Word e,x∈(candidateWords e).result) ∧
    (candidateWords e).steps=candidateFee e := by
  let n := (2:ℕ)^e-1
  have hpow : 0<(2:ℕ)^e := by positivity
  have hn : n<2^e := by unfold n; omega
  obtain ⟨rows,charge⟩ := positive_tape_exact e n he hn
  refine ⟨?_,?_,?_⟩
  · change (wordZero e::(positiveTape e n).result).length=_
    rw [rows,List.length_cons,List.length_ofFn]
    unfold n
    omega
  · intro x
    let j := bitsValue x.val
    have hj : j<2^e := by
      simpa only [x.property] using bitsValue_lt x.val
    change x∈wordZero e::(positiveTape e n).result
    rw [List.mem_cons]
    by_cases hz : j=0
    · left
      apply Subtype.ext
      apply equal_width_inj _ _
      · rw [x.property,(wordZero e).property]
      · change j=bitsValue (List.replicate e false)
        rw [hz,value_zero]
    · have hFin : j-1<n := by unfold n; omega
      let i : Fin n := ⟨j-1,hFin⟩
      right
      rw [rows,List.mem_ofFn]
      refine ⟨i,?_⟩
      apply Subtype.ext
      apply equal_width_inj _ _
      · exact (encoded e (i.val+1)).property.trans x.property.symm
      · change bitsValue (encodeBits e (i.val+1))=j
        have E : i.val+1=j := by unfold i; dsimp; omega
        rw [E,encodeBits_exact e j hj]
  · change (positiveTape e n).steps+4*e+5=candidateFee e
    rw [charge]
    rfl

def divisorWords : (d : ℕ)→Meter (List (List Bool))
  | 0 => ⟨[],3⟩
  | d+1 =>
    let r := candidateWords (d+1)
    let tail := divisorWords d
    ⟨r.result.map Subtype.val++tail.result,
      r.steps+tail.steps+r.result.length*(4*(d+1)+10)+5⟩

def divisorCount (d : ℕ) := 2^(d+1)-2

def divisorFee : ℕ→ℕ
  | 0=>3
  | d+1=>candidateFee (d+1)+divisorFee d+2^(d+1)*(4*(d+1)+10)+5

theorem divisor_words_exact (d : ℕ) :
    (∀ x : List Bool, x∈(divisorWords d).result ↔ 0<x.length ∧ x.length≤d) ∧
    (divisorWords d).result.length=divisorCount d ∧
    (divisorWords d).steps=divisorFee d := by
  induction d with
  | zero =>
    refine ⟨?_,rfl,rfl⟩
    intro x
    constructor
    · simp [divisorWords]
    · intro h
      omega
  | succ d recorded =>
    obtain ⟨mem,len,fee⟩ := recorded
    let r := candidateWords (d+1)
    have R := candidate_words_exact (d+1) (by omega)
    refine ⟨?_,?_,?_⟩
    · intro x
      change x∈r.result.map Subtype.val++(divisorWords d).result ↔ _
      rw [List.mem_append,List.mem_map,mem x]
      constructor
      · rintro (⟨y,hy,hv⟩|h)
        · rw [←hv,y.property]
          omega
        · omega
      · intro xfit
        by_cases h : x.length=d+1
        · exact Or.inl ⟨⟨x,h⟩,R.2.1 ⟨x,h⟩,rfl⟩
        · exact Or.inr ⟨xfit.1,by omega⟩
    · change (r.result.map Subtype.val++(divisorWords d).result).length=_
      rw [List.length_append,List.length_map,R.1,len]
      unfold divisorCount
      rw [pow_succ 2 (d+1)]
      have h : 2≤(2:ℕ)^(d+1) := by
        rw [pow_succ 2 d]
        have p : 0<(2:ℕ)^d := by positivity
        omega
      omega
    · change r.steps+(divisorWords d).steps+r.result.length*(4*(d+1)+10)+5=_
      rw [R.2.2,fee,R.1]
      rfl

#print axioms equal_width_inj
#print axioms candidate_words_exact
#print axioms divisor_words_exact
end J6R29BinaryFieldSearch
