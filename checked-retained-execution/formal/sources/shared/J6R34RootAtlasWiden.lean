import J6R33StatefulArithmeticPageCore

/-! Root Pages are initially serialized in their actual source local
width. Widening to a common tree ABI physically copies their bits and
writes a zero suffix; it changes neither the typed Page nor the
immutable payload. It is not a cast identifying differently sized
external words. -/
namespace J6R34RootAtlas
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R30ProducedGateRegistry

def suffixZeros : ℕ→Meter (List Bool)
  | 0=>⟨[],1⟩
  | n+1=>let z := suffixZeros n; ⟨false::z.result,z.steps+3⟩

theorem suffix_exact (n : ℕ) : suffixZeros n=⟨List.replicate n false,3*n+1⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [suffixZeros,ih]
    simp only [List.replicate_succ]
    congr 1

def copyOnto (tail : List Bool) : List Bool→Meter (List Bool)
  | []=>⟨tail,1⟩
  | b::bs=>let pasted := copyOnto tail bs; ⟨b::pasted.result,pasted.steps+3⟩

theorem copy_onto_exact (tail bits : List Bool) : copyOnto tail bits=⟨bits++tail,3*bits.length+1⟩ := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    rw [copyOnto,ih]
    simp only [List.cons_append,List.length_cons]
    congr 1

def widened {n : ℕ} (ext : ℕ) (addr : Word n) : Meter (Word (n+ext)) :=
  let z := suffixZeros ext
  let pasted := copyOnto z.result addr.bits
  ⟨⟨pasted.result,by
     change (copyOnto (suffixZeros ext).result addr.bits).result.length=n+ext
     rw [suffix_exact,copy_onto_exact]
     simp only [List.length_append,List.length_replicate,addr.size]⟩,z.steps+pasted.steps+2⟩

def wideningFee (n ext : ℕ) := 3*n+3*ext+4

theorem widened_exact {n : ℕ} (ext : ℕ) (addr : Word n) :
    (widened ext addr).result.bits=addr.bits++List.replicate ext false ∧
    (widened ext addr).steps=wideningFee n ext := by
  unfold widened wideningFee
  dsimp only
  rw [suffix_exact,copy_onto_exact]
  dsimp only
  rw [addr.size]
  exact ⟨rfl, by omega⟩

theorem widened_distinct {n : ℕ} (ext : ℕ) :
    Function.Injective (fun addr : Word n=>(widened ext addr).result) := by
  intro x y eq
  have h := congrArg Word.bits eq
  rw [(widened_exact ext x).1,(widened_exact ext y).1] at h
  have E := (List.append_inj h (x.size.trans y.size.symm)).1
  cases x
  cases y
  simp_all

def widenRows {n : ℕ} {D : Type*} (ext : ℕ) : List (RefRow n D)→Meter (List (RefRow (n+ext) D))
  | []=>⟨[],2⟩
  | x::xs=>
    let key := widened ext x.address
    let tail := widenRows ext xs
    ⟨⟨key.result,x.payload⟩::tail.result,key.steps+tail.steps+7⟩

def mappedRow {n : ℕ} {D : Type*} (ext : ℕ) (x : RefRow n D) : RefRow (n+ext) D :=
  ⟨(widened ext x.address).result,x.payload⟩

theorem widened_rows_exact {n : ℕ} {D : Type*} (ext : ℕ) (rows : List (RefRow n D)) :
    widenRows ext rows=⟨rows.map (mappedRow ext),2+rows.length*(wideningFee n ext+7)⟩ := by
  induction rows with
  | nil => simp only [widenRows,List.map_nil,List.length_nil,Nat.zero_mul,Nat.add_zero]
  | cons x xs ih =>
    rw [widenRows,ih,(widened_exact ext x.address).2]
    simp only [List.map_cons,mappedRow,List.length_cons,Nat.add_mul,Nat.one_mul]
    congr 1
    omega

theorem widened_lookup_same {n : ℕ} {D : Type*} (ext : ℕ) (rows : List (RefRow n D)) (addr : Word n) :
    (locate (widened ext addr).result (widenRows ext rows).result).result=(locate addr rows).result := by
  rw [widened_rows_exact]
  dsimp only
  induction rows with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    by_cases h : x.address=addr
    · subst addr
      rw [ref_head_exact x xs,show (widened ext x.address).result=(mappedRow ext x).address from rfl,
        ref_head_exact]
      rfl
    · have hh : (mappedRow ext x).address≠(widened ext addr).result := fun e=>h (widened_distinct ext e)
      rw [ref_old_exact (mappedRow ext x) _ _ hh,ref_old_exact x xs addr h,ih]

#print axioms widened_exact
#print axioms widened_distinct
#print axioms widened_rows_exact
#print axioms widened_lookup_same
end J6R34RootAtlas
