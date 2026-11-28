import J4R43LiteralOutsideVariableElim
import Mathlib.Data.Fin.Tuple.Basic

/-! A finite binary table is materialized as an actual tree. Each
lookup reads precisely one edge per coordinate, and it never
re-evaluates a previous bucket. -/
namespace J4R43LiteralOutside.VE
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

inductive BoolTable (R : Type) : ℕ→Type
  | leaf : R→BoolTable R 0
  | branch {n : ℕ} : BoolTable R n→BoolTable R n→BoolTable R (n+1)

variable {R : Type}

def tabulate : (n : ℕ)→((Fin n→Bool)→R)→BoolTable R n
  | 0, f => .leaf (f (fun u=>Fin.elim0 u))
  | n+1, f => .branch (tabulate n (fun z=>f (Fin.cons false z)))
      (tabulate n (fun z=>f (Fin.cons true z)))

def readTable : {n : ℕ}→BoolTable R n→(Fin n→Bool)→R×ℕ
  | _, .leaf x, _ => (x,0)
  | _, .branch lo hi, w =>
    let q := if w 0 then readTable hi (w ∘ Fin.succ) else readTable lo (w ∘ Fin.succ)
    (q.1,q.2+1)

theorem read_table_exact (n : ℕ) (f : (Fin n→Bool)→R) (w : Fin n→Bool) :
    readTable (tabulate n f) w = (f w,n) := by
  induction n with
  | zero =>
    have e : (fun u : Fin 0=>Fin.elim0 u)=w := by funext u; exact Fin.elim0 u
    simp only [tabulate,readTable,e]
  | succ n ih =>
    have h : Fin.cons (w 0) (w ∘ Fin.succ)=w := by
      exact Fin.cons_self_tail w
    cases e : w 0
    · simp only [tabulate,readTable,e,Bool.false_eq_true,if_false,ih]
      rw [e] at h
      rw [h]
    · simp only [tabulate,readTable,e,if_true,ih]
      rw [e] at h
      rw [h]

def leaves : {n : ℕ}→BoolTable R n→ℕ
  | _, .leaf _ => 1
  | _, .branch lo hi => leaves lo+leaves hi

theorem leaves_count {n : ℕ} (T : BoolTable R n) :
    leaves T=2^n := by
  induction T with
  | leaf _ => rfl
  | @branch n lo hi x y => simp only [leaves,x,y,pow_succ]; omega

variable {V : Type} [Fintype V] [DecidableEq V] [CommRing R]

def scopeOrder (s : Finset V) : Fin s.card ≃ s :=
  (finCongr (Fintype.card_coe s).symm).trans (Fintype.equivFin s).symm

def savedTable (F : Factor V R) : BoolTable R F.scope.card :=
  tabulate F.scope.card (fun w=>F.table (w ∘ (scopeOrder F.scope).symm))

def storedFactor (F : Factor V R) : Factor V R :=
  ⟨F.scope,fun v=>(readTable (savedTable F) (v ∘ scopeOrder F.scope)).1⟩

theorem stored_factor_exact (F : Factor V R) : storedFactor F=F := by
  cases F with
  | mk scope f =>
    change { scope:=scope, table:=_ : Factor V R }={ scope:=scope, table:=f }
    congr 1
    funext z
    unfold savedTable
    rw [read_table_exact]
    change f ((z ∘ scopeOrder scope) ∘ (scopeOrder scope).symm)=f z
    congr 1
    funext u
    simp

def eliminateStored (v : V) (fs : List (Factor V R)) : List (Factor V R) :=
  storedFactor (updateFactor v fs) :: outside v fs

theorem stored_elimination_exact (v : V) (fs : List (Factor V R)) :
    eliminateStored v fs = eliminate v fs := by simp [eliminateStored,eliminate,stored_factor_exact]

def bucketArithmetic (v : V) (fs : List (Factor V R)) : ℕ :=
  leaves (savedTable (updateFactor v fs))*(2*(inside v fs).length+1)

theorem exact_bucket_arithmetic (v : V) (fs : List (Factor V R)) :
    bucketArithmetic v fs=2^(bucketScope v fs).card*(2*(inside v fs).length+1) := by
  unfold bucketArithmetic
  rw [leaves_count]
  rfl

theorem bounded_bucket_arithmetic (v : V) (fs : List (Factor V R)) (w : ℕ)
    (B : (bucketScope v fs).card≤w) :
    bucketArithmetic v fs≤2^w*(2*fs.length+1) := by
  rw [exact_bucket_arithmetic]
  apply Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) B)
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (List.length_filter_le (fun f : Factor V R=>decide (v∈f.scope)) fs)) _

#print axioms read_table_exact
#print axioms leaves_count
#print axioms stored_factor_exact
#print axioms stored_elimination_exact
#print axioms exact_bucket_arithmetic
#print axioms bounded_bucket_arithmetic
end
end J4R43LiteralOutside.VE

