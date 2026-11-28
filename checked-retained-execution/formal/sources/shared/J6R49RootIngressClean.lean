import J7R9Clause
import J6R27OriginalGateModeCompare

/-! R49 original root ingress, starting from raw variable-name words and
literal sign bits. The cleanup reads actual bytes, retains empty clauses,
drops just the syntactic tautologies, and keeps precisely the original
last-occurrence deduplication order. -/
namespace J6R49RootIngress
open Std.Sat AOracleMachineTime J6R27OriginalGate J6R15ModeCost J6R21Ancestor
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5200000

abbrev BitsLit := List Bool × Bool
abbrev BitsClause := CNF.Clause (List Bool)
abbrev BitsCNF := CNF (List Bool)

def hasLiteral (q : BitsLit) : BitsClause → Meter Bool
  | [] => ⟨false,1⟩
  | a::as =>
    let h := eqRawBits q.1 a.1
    let rest := hasLiteral q as
    ⟨((q.2 == a.2) && h.result) || rest.result,h.steps+rest.steps+5⟩

theorem has_literal_exact (q : BitsLit) (xs : BitsClause) :
    ((hasLiteral q xs).result = true ↔ q ∈ xs) ∧
      (hasLiteral q xs).steps ≤ 1+xs.length*(5*q.1.length+7) := by
  induction xs with
  | nil => simp [hasLiteral]
  | cons a as ih =>
    obtain ⟨hEq,hFee⟩ := eq_raw_bits_exact q.1 a.1
    constructor
    · simp only [hasLiteral,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,hEq,ih.1,List.mem_cons]
      simp only [Prod.ext_iff]
      exact ⟨fun h => h.elim (fun x => Or.inl ⟨x.2,x.1⟩) Or.inr,
        fun h => h.elim (fun x => Or.inl ⟨x.2,x.1⟩) Or.inr⟩
    · simp only [hasLiteral,List.length_cons,Nat.succ_mul]
      linarith only [hFee,ih.2]

def hasOpposite (all : BitsClause) : BitsClause → Meter Bool
  | [] => ⟨false,1⟩
  | a::as =>
    let row := hasLiteral (a.1,!a.2) all
    let tail := hasOpposite all as
    ⟨row.result || tail.result,row.steps+tail.steps+4⟩

theorem has_opposite_exact (all xs : BitsClause) :
    (hasOpposite all xs).result = true ↔ ∃ a∈xs,(a.1,!a.2)∈all := by
  induction xs with
  | nil => simp [hasOpposite]
  | cons a as ih =>
    simp only [hasOpposite,Bool.or_eq_true,(has_literal_exact _ _).1,ih,List.mem_cons]
    constructor
    · rintro (h|⟨x,hx,h⟩)
      · exact ⟨a,Or.inl rfl,h⟩
      · exact ⟨x,Or.inr hx,h⟩
    · rintro ⟨x,rfl|hx,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨x,hx,h⟩

theorem has_opposite_steps (all xs : BitsClause) (w : ℕ)
    (shape : ∀ a∈xs,a.1.length=w) :
    (hasOpposite all xs).steps ≤ 1+xs.length*(5+all.length*(5*w+7)) := by
  induction xs with
  | nil => simp [hasOpposite]
  | cons a as ih =>
    have E := (has_literal_exact (a.1,!a.2) all).2
    change (hasLiteral (a.1,!a.2) all).steps≤1+all.length*(5*a.1.length+7) at E
    rw [shape _ (List.mem_cons_self)] at E
    have Q := ih (fun x hx => shape x (List.mem_cons_of_mem _ hx))
    simp only [hasOpposite,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

def copyDedup : BitsClause→Meter BitsClause
  | [] => ⟨[],1⟩
  | a::as =>
    let test := hasLiteral a as
    let tail := copyDedup as
    if test.result then ⟨tail.result,test.steps+tail.steps+3⟩
    else let copy := copyBytes a.1
         ⟨(copy.result,a.2)::tail.result,test.steps+tail.steps+copy.steps+3⟩

theorem copy_dedup_exact (xs : BitsClause) : (copyDedup xs).result=xs.dedup := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    by_cases hx : a∈as
    · have h := (has_literal_exact a as).1.mpr hx
      simp [copyDedup,h,ih,List.dedup_cons_of_mem hx]
    · have h : (hasLiteral a as).result=false :=
        Bool.eq_false_iff.mpr (fun h => hx ((has_literal_exact a as).1.mp h))
      simp only [copyDedup,h,Bool.false_eq_true,if_false,copyBytes_exact,ih,
        List.dedup_cons_of_notMem hx,Prod.eta]

theorem copy_dedup_steps (xs : BitsClause) (w k : ℕ)
    (size : xs.length≤k) (shape : ∀ a∈xs,a.1.length=w) :
    (copyDedup xs).steps ≤ 1+xs.length*(5+3*w+k*(5*w+7)) := by
  induction xs with
  | nil => simp [copyDedup]
  | cons a as ih =>
    have aW := shape _ (List.mem_cons_self)
    have asK : as.length≤k := by simp only [List.length_cons] at size; omega
    have E := (has_literal_exact a as).2
    rw [aW] at E
    have E' := E.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (5*w+7) asK) 1)
    have Q := ih asK (fun x hx => shape x (List.mem_cons_of_mem _ hx))
    have C := congrArg Meter.steps (copyBytes_exact a.1)
    change (copyBytes a.1).steps=3*a.1.length+1 at C
    rw [aW] at C
    by_cases ht : (hasLiteral a as).result=true <;>
      simp only [copyDedup,ht,if_true,if_false,Bool.false_eq_true,List.length_cons] <;>
      rw [Nat.add_mul,Nat.one_mul] <;> omega

def cleanMeter : BitsCNF→Meter BitsCNF
  | [] => ⟨[],1⟩
  | c::F =>
    let taut := hasOpposite c c
    let tail := cleanMeter F
    if taut.result then ⟨tail.result,taut.steps+tail.steps+3⟩
    else let row := copyDedup c
         ⟨row.result::tail.result,taut.steps+row.steps+tail.steps+3⟩

theorem clean_meter_exact (F : BitsCNF) : (cleanMeter F).result=J7R9Clause.clean F := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    have T : (hasOpposite c c).result=J7R9Clause.taut c :=
      Bool.eq_iff_iff.mpr ((has_opposite_exact c c).trans (J7R9Clause.taut_true c).symm)
    cases ht : J7R9Clause.taut c <;> simp [cleanMeter,T,ht,ih,copy_dedup_exact,J7R9Clause.clean]

def cleanFee (w k : ℕ) : ℕ := 5+k*(5+k*(5*w+7))+k*(5+3*w+k*(5*w+7))

theorem clean_meter_steps (F : BitsCNF) (w k : ℕ)
    (size : ∀ c∈F,c.length≤k) (shape : ∀ c∈F,∀ a∈c,a.1.length=w) :
    (cleanMeter F).steps≤1+F.length*cleanFee w k := by
  induction F with
  | nil => simp [cleanMeter]
  | cons c F ih =>
    have hC := size _ (List.mem_cons_self)
    have hW := shape _ (List.mem_cons_self)
    have Q := ih (fun x hx => size x (List.mem_cons_of_mem _ hx))
      (fun x hx => shape x (List.mem_cons_of_mem _ hx))
    have D := copy_dedup_steps c w k hC hW
    have D' := D.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hC) 1)
    have T := has_opposite_steps c c w hW
    have i := Nat.add_le_add_left (Nat.mul_le_mul_right (5*w+7) hC) 5
    have T' := T.trans (Nat.add_le_add_left (Nat.mul_le_mul hC i) 1)
    by_cases h : (hasOpposite c c).result=true <;>
      simp only [cleanMeter,h,if_true,if_false,Bool.false_eq_true,List.length_cons] <;>
      rw [Nat.add_mul,Nat.one_mul] <;> simp only [cleanFee] at Q ⊢ <;> omega

#print axioms has_literal_exact
#print axioms has_opposite_exact
#print axioms has_opposite_steps
#print axioms copy_dedup_exact
#print axioms copy_dedup_steps
#print axioms clean_meter_exact
#print axioms clean_meter_steps
end J6R49RootIngress
