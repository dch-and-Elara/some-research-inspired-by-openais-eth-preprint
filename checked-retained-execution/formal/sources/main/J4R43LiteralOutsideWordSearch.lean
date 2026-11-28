import J4R43LiteralOutsideBitStrip

/-! Fixed-width decoder primitive: compare word bits and update a
candidate by actual modular multiplication. The fee counts both,
rather than asking an arbitrary-precision integer oracle to compare. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6800000

theorem exact_bits_value_injective {x y : List Bool}
    (length : x.length=y.length) (value : bitsValue x=bitsValue y) :
    x=y := by
  induction x generalizing y with
  | nil => exact (List.length_eq_zero_iff.mp length.symm).symm
  | cons a s ih =>
    cases y with
    | nil => simp at length
    | cons b t =>
      have len : s.length=t.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using length
      cases a <;> cases b <;>
        simp only [true_low_value,false_low_value] at value
      · exact congrArg (List.cons false) (ih len (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih len (by omega))

theorem every_unsigned_word_value_fits (x : List Bool) : bitsValue x<2^x.length := by
  induction x with
  | nil => decide
  | cons b xs ih =>
    cases b <;> simp only [false_low_value,true_low_value,List.length_cons,pow_succ] <;> omega

theorem pword_value_eq {p : ℕ} (x : Word p) :
    (wordRead x).val=bitsValue x.val := by
  change ((bitsValue x.val:ℕ):ZMod (2^p)).val=_
  apply ZMod.val_natCast_of_lt
  have b := every_unsigned_word_value_fits x.val
  rwa [x.property] at b

theorem pword_same_read {p : ℕ} {x y : Word p} :
    wordRead x=wordRead y ↔ x.val=y.val := by
  constructor
  · intro e
    apply exact_bits_value_injective (x.property.trans y.property.symm)
    have h := congrArg ZMod.val e
    simpa only [pword_value_eq] using h
  · intro e
    exact congrArg wordRead (Subtype.ext e)

def compareTape : List Bool→List Bool→Bool×ℕ
  | [],[] => (true,1)
  | a::as,b::bs =>
    if a=b then
      let r := compareTape as bs
      (r.1,r.2+1)
    else (false,1)
  | _,_ => (false,1)

theorem raw_compare_exact (x y : List Bool) :
    (compareTape x y).1=true ↔ x=y := by
  induction x generalizing y with
  | nil => cases y <;> simp [compareTape]
  | cons a s ih =>
    cases y with
    | nil => simp [compareTape]
    | cons b t =>
      by_cases E : a=b
      · simp [compareTape,E,ih]
      · simp [compareTape,E]

theorem raw_compare_fee (x y : List Bool) :
    (compareTape x y).2≤x.length+1 := by
  induction x generalizing y with
  | nil => cases y <;> simp [compareTape]
  | cons a s ih =>
    cases y with
    | nil => simp [compareTape]
    | cons b t =>
      by_cases E : a=b
      · have h := ih t
        simp only [compareTape,if_pos E,List.length_cons]
        omega
      · simp [compareTape,E]

def checkCandidate {p : ℕ} (seen init : Word p) :=
  compareTape seen.val init.val

theorem candidate_matches_iff {p : ℕ} (seen init : Word p) :
    (checkCandidate seen init).1=true ↔ wordRead seen=wordRead init :=
  (raw_compare_exact _ _).trans pword_same_read.symm

def nativeHammingWord {p : ℕ} (seen base init : Word p) : ℕ→Meter ℕ
  | 0 => ⟨0,0⟩
  | 1 =>
    let c := checkCandidate seen init
    if c.1 then ⟨0,c.2⟩ else ⟨1,c.2⟩
  | n+2 =>
    let c := checkCandidate seen init
    if c.1 then ⟨0,c.2⟩ else
      let m := mulWord init base
      let r := nativeHammingWord seen base m.result (n+1)
      ⟨r.result+1,c.2+m.steps+r.steps+3⟩

theorem native_hamming_word_fee {p : ℕ} (hp : 0<p) (seen base init : Word p) (n : ℕ) :
    (nativeHammingWord seen base init n).steps≤n*(wordOpCap p+p+4) := by
  induction n generalizing init with
  | zero => simp [nativeHammingWord]
  | succ n ih =>
    have f : (checkCandidate seen init).2≤p+1 := by
      unfold checkCandidate
      simpa only [seen.property] using raw_compare_fee seen.val init.val
    have m := (wordOps p hp).mul_cost init base
    change (mulWord init base).steps≤wordOpCap p at m
    cases n with
    | zero =>
      dsimp only [nativeHammingWord]
      split <;> dsimp only <;> omega
    | succ n =>
      have next := ih (mulWord init base).result
      dsimp only [nativeHammingWord]
      rw [Nat.succ_mul (n+1)]
      split <;> dsimp only <;> omega

theorem native_hamming_word_correct {p : ℕ} (seen base init : Word p) {n j : ℕ}
    (valid : j<n)
    (unique : ∀ i<n,wordRead seen=wordRead init*(wordRead base)^i ↔ i=j) :
    (nativeHammingWord seen base init n).result=j := by
  induction n generalizing init j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero =>
      have yes : wordRead seen=wordRead init := by
        simpa using (unique 0 (Nat.zero_lt_succ n)).mpr rfl
      have ok := (candidate_matches_iff seen init).mpr yes
      cases n <;> simp [nativeHammingWord,ok]
    | succ j =>
      cases n with
      | zero => omega
      | succ n =>
        have no : (checkCandidate seen init).1≠true := by
          intro yes
          have eq := (candidate_matches_iff seen init).mp yes
          have z := (unique 0 (by omega)).mp (by simpa using eq)
          omega
        have next (i : ℕ) (h : i<n+1) :
            wordRead seen=wordRead (mulWord init base).result*(wordRead base)^i ↔ i=j := by
          rw [mulWord_read]
          have e : (wordRead init*wordRead base)*(wordRead base)^i=
             wordRead init*(wordRead base)^(i+1) := by rw [pow_succ']; ring
          rw [e,unique (i+1) (by omega)]
          exact Nat.succ_inj
        have run := ih (init:=(mulWord init base).result) (j:=j) (by omega) next
        dsimp only [nativeHammingWord]
        rw [if_neg no,run]

#print axioms exact_bits_value_injective
#print axioms pword_same_read
#print axioms raw_compare_exact
#print axioms raw_compare_fee
#print axioms native_hamming_word_fee
#print axioms native_hamming_word_correct
end
end J4R43LiteralOutside

