
import J6R29BinaryFieldSearchDivisor
import J6R29BinaryFieldSearchEnum
import J6R29BinaryFieldSearchField

/-! The printed deterministic finite-field selection: exhaustive binary
monic candidates, exhaustive proper half-degree monic divisors, first
passing candidate. Arithmetic is one-bit polynomial reduction; tape
production and every inspected trial are charged. -/
namespace J6R29BinaryFieldSearch
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime AOracleMachineTimeMul
open J6R28GeneratedRootFrame
set_option maxHeartbeats 7200000
set_option maxRecDepth 1800

def trialUpper (e : ℕ) : ℕ :=
  (4+10*e)+(4+10*e)+(3+6*(e+1))+(e+1)*(e+1)*264+(3+6*e)+8

theorem trial_fee_upper (e d : ℕ) (h : d≤e) : divisorTrialFee e d≤trialUpper e := by
  have q : (e+1-d)*(d+1)*264≤(e+1)*(e+1)*264 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.add_le_add_right h 1))
  unfold divisorTrialFee trialUpper
  omega

def rejectAllDivisors (f : List Bool) : List (List Bool)→Meter Bool
  | [] => ⟨true,4⟩
  | g::gs =>
    let B := binaryDivisorTest f g
    let R := rejectAllDivisors f gs
    ⟨!B.result && R.result,B.steps+R.steps+6⟩

theorem reject_all_divisors_exact (f : List Bool) (D : List (List Bool))
    (well : ∀ g∈D, 0<g.length ∧ g.length≤f.length/2) :
    ((rejectAllDivisors f D).result=true ↔
      ∀ g∈D,¬binaryPolynomial (ZMod 2) g ∣ binaryPolynomial (ZMod 2) f) ∧
      (rejectAllDivisors f D).steps≤4+D.length*(trialUpper f.length+6) := by
  induction D with
  | nil => simp [rejectAllDivisors]
  | cons g gs ih =>
    have hd := well g (List.mem_cons.mpr (Or.inl rfl))
    have fit : g.length≤f.length := hd.2.trans (Nat.div_le_self _ _)
    have test := binary_divisor_trial f g hd.1 (fit.trans (Nat.le_succ _))
    have rest := ih (fun g' hg' => well g' (List.mem_cons.mpr (Or.inr hg')))
    have notTest : (binaryDivisorTest f g).result=false ↔
        ¬binaryPolynomial (ZMod 2) g ∣ binaryPolynomial (ZMod 2) f := by
      rw [←test.1]
      cases (binaryDivisorTest f g).result <;> decide
    constructor
    · change (!(binaryDivisorTest f g).result && (rejectAllDivisors f gs).result)=true ↔ _
      rw [Bool.and_eq_true,Bool.not_eq_true',notTest,rest.1]
      constructor
      · rintro ⟨primary,remaining⟩ h hh
        rcases List.mem_cons.mp hh with X|X
        · exact X ▸ primary
        · exact remaining h X
      · intro H
        exact ⟨H g (List.mem_cons.mpr (Or.inl rfl)),
          fun g' hg' => H g' (List.mem_cons.mpr (Or.inr hg'))⟩
    · change (binaryDivisorTest f g).steps+(rejectAllDivisors f gs).steps+6≤_
      have n := test.2.trans (trial_fee_upper f.length g.length fit)
      have b := rest.2
      rw [List.length_cons,Nat.succ_mul]
      omega

def wordCheck (e : ℕ) (w : Word e) (D : List (List Bool)) : Meter Bool :=
  rejectAllDivisors w.val D

theorem word_check_exact (e : ℕ) (he : 0<e) (w : Word e) :
    ((wordCheck e w (divisorWords (e/2)).result).result=true ↔
      Irreducible (NativeProbeRing.residuePoly (chosenBinaryPolynomial w))) ∧
      (wordCheck e w (divisorWords (e/2)).result).steps
        ≤4+divisorCount (e/2)*(trialUpper e+6) := by
  let D := (divisorWords (e/2)).result
  have W := divisor_words_exact (e/2)
  have well : ∀ g∈D,0<g.length∧g.length≤w.val.length/2 := by
    intro g hg
    rw [w.property]
    exact (W.1 g).mp hg
  have C := reject_all_divisors_exact w.val D well
  constructor
  · change (rejectAllDivisors w.val D).result=true ↔ _
    rw [source_residue_of_tape,proper_binary_divisors w.val (w.property.symm ▸ he),C.1]
    constructor
    · intro all g pos lim
      exact all g ((W.1 g).mpr ⟨pos,w.property ▸ lim⟩)
    · exact fun all g hg => all g (well g hg).1 (well g hg).2
  · change (rejectAllDivisors w.val D).steps≤_
    simpa only [show D.length=divisorCount (e/2) from W.2.1,w.property] using C.2

def firstPassing (e : ℕ) (probe : Word e→Meter Bool) :
    List (Word e)→Meter (Option (Word e))
  | []=>⟨none,4⟩
  | t::ts=>
    let B := probe t
    if B.result then
      ⟨some t,B.steps+e+6⟩
    else
      let R := firstPassing e probe ts
      ⟨R.result,B.steps+R.steps+e+6⟩

def ValidProbeAnswer {e : ℕ} (probe : Word e→Meter Bool) (xs : List (Word e)) :
    Option (Word e)→Prop
  | some x=>x∈xs ∧ (probe x).result=true
  | none=>∀ x∈xs,(probe x).result=false

theorem first_passing_receipt (e cap : ℕ) (probe : Word e→Meter Bool)
    (bounded : ∀ w,(probe w).steps≤cap) (xs : List (Word e)) :
    ValidProbeAnswer probe xs (firstPassing e probe xs).result ∧
    (firstPassing e probe xs).steps≤4+xs.length*(cap+e+6) := by
  induction xs with
  | nil => simp [firstPassing,ValidProbeAnswer]
  | cons x xs ih =>
    have n := bounded x
    have q := ih.2
    cases h : (probe x).result
    · have ze : (firstPassing e probe (x::xs)).result=(firstPassing e probe xs).result := by
        simp [firstPassing,h]
      have ce : (firstPassing e probe (x::xs)).steps =
          (probe x).steps+(firstPassing e probe xs).steps+e+6 := by
        simp [firstPassing,h]
      rw [ze,ce,List.length_cons,Nat.succ_mul]
      refine ⟨?_,by omega⟩
      have z := ih.1
      cases R : (firstPassing e probe xs).result with
      | none =>
        rw [R] at z
        intro y hy
        rcases List.mem_cons.mp hy with X|X
        · exact X ▸ h
        · exact z y X
      | some y =>
        rw [R] at z
        exact ⟨List.mem_cons.mpr (Or.inr z.1),z.2⟩
    · have ze : (firstPassing e probe (x::xs)).result=some x := by
        simp [firstPassing,h]
      have ce : (firstPassing e probe (x::xs)).steps=(probe x).steps+e+6 := by
        simp [firstPassing,h]
      rw [ze,ce,List.length_cons,Nat.succ_mul]
      exact ⟨⟨List.mem_cons.mpr (Or.inl rfl),h⟩,by omega⟩

def fieldSearch (e : ℕ) : Meter (Option (Word e)) :=
  let A := candidateWords e
  let B := divisorWords (e/2)
  let R := firstPassing e (fun w=>wordCheck e w B.result) A.result
  ⟨R.result,A.steps+B.steps+R.steps+6⟩

def fieldSearchFee (e : ℕ) : ℕ :=
  candidateFee e+divisorFee (e/2)+4+2^e*(4+divisorCount (e/2)*(trialUpper e+6)+e+6)+6

theorem field_search_success (e : ℕ) (he : 0<e) :
    ∃ w : Word e,(fieldSearch e).result=some w ∧
      Irreducible (NativeProbeRing.residuePoly (chosenBinaryPolynomial w)) ∧
      (fieldSearch e).steps≤fieldSearchFee e := by
  let A := candidateWords e
  let B := divisorWords (e/2)
  let probe := fun w=>wordCheck e w B.result
  let run := firstPassing e probe A.result
  obtain ⟨aLen,aAll,aFee⟩ := candidate_words_exact e he
  have bFee : B.steps=divisorFee (e/2) := (divisor_words_exact (e/2)).2.2
  obtain ⟨sem,cost⟩ := first_passing_receipt e
    (4+divisorCount (e/2)*(trialUpper e+6)) probe
    (fun w=>(word_check_exact e he w).2) A.result
  change ValidProbeAnswer probe A.result run.result at sem
  change run.steps≤4+A.result.length*(4+divisorCount (e/2)*(trialUpper e+6)+e+6) at cost
  have bill : (fieldSearch e).steps≤fieldSearchFee e := by
    change A.steps+B.steps+run.steps+6≤_
    change A.steps=candidateFee e at aFee
    change A.result.length=2^e at aLen
    rw [aLen] at cost
    rw [aFee,bFee]
    unfold fieldSearchFee
    omega
  cases status : run.result with
  | none =>
    rw [status] at sem
    obtain ⟨w,I⟩ := exists_binary_field_tape e he
    have h := sem w (aAll w)
    have pass : (probe w).result=true := (word_check_exact e he w).1.mpr
      ((source_residue_of_tape w).symm ▸ I)
    rw [pass] at h
    contradiction
  | some w =>
    rw [status] at sem
    exact ⟨w,status,(word_check_exact e he w).1.mp sem.2,bill⟩

#print axioms trial_fee_upper
#print axioms reject_all_divisors_exact
#print axioms word_check_exact
#print axioms first_passing_receipt
#print axioms field_search_success
end J6R29BinaryFieldSearch
