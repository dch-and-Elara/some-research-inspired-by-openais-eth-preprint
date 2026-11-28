
import J6R19RetainedWords
import J6R19RetainedBox

/-! Executable finite retention regression.  An original Boolean Plant
gate can only store 0 or 1.  The numeric witness 7 belongs to a generic
generated old entry, whose same-word precision conversion is exactly
the resizeUV used by R21 invokeTrace and justified by native_resizeUV. -/
namespace J6R27OriginalGate
open AOracleMachineTime AOracleMachineTimeTape A1R10 J6R19Retained

def oneWord {p : ℕ} (v : ℕ) : A1R10.Word p := ⟨encodeBits p v,encodeBits_length p v⟩

def scalarFrame (p : ℕ) : List (A1R10.Word p) := [oneWord 0]

def scalarTest (p v : ℕ) : UVBlock (scalarFrame p) 1 :=
  ⟨[⟨[oneWord v],rfl⟩],rfl⟩

def readTestScalar {p : ℕ} (x : UVBlock (scalarFrame p) 1) : ℕ :=
  ((x.val.head?.bind (fun z=>z.val.head?)).map (fun b=>bitsValue b.val)).getD 0

def wideningRegression : Meter (UVBlock (scalarFrame 3) 1) :=
  resizeUV (old:=scalarFrame 2) (new:=scalarFrame 3) rfl (scalarTest 2 7)

theorem created_word_7_reads_3 :
    readTestScalar (scalarTest 2 7)=3 ∧ readTestScalar wideningRegression.result=3 ∧
      readTestScalar (scalarTest 3 7)=7 := by decide

theorem widening_is_not_a_fresh_evaluation :
    wideningRegression.result≠scalarTest 3 7 := by
  intro e
  have h := congrArg readTestScalar e
  rw [created_word_7_reads_3.2.1,created_word_7_reads_3.2.2] at h
  cases h

#print axioms created_word_7_reads_3
#print axioms widening_is_not_a_fresh_evaluation
end J6R27OriginalGate

