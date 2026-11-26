import P5EscapeE2Canonical
import A1R10Word

/-! The high-rank matrix is obtained by the concrete low-width
two's-complement subtraction.  Bit-operation counts are from the existing
tape meter, not a postulated cost per ring operation. -/
namespace Paper5.EscapeE2
open A1R10 AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul

def indexOfWord {m : ℕ} (a : Word m) : Fin (2^m) :=
  ⟨bitsValue a.val,by simpa only [a.property] using bitsValue_lt a.val⟩

def wordOfIndex {m : ℕ} (a : Fin (2^m)) : Word m :=
  ⟨encodeBits m a.val,encodeBits_length m a.val⟩

@[simp] theorem index_of_index_word {m : ℕ} (a : Fin (2^m)) :
    indexOfWord (wordOfIndex a)=a := by
  apply Fin.ext
  exact encodeBits_exact m a.val a.isLt

theorem word_read_val {m : ℕ} (a : Word m) : (wordRead a).val=bitsValue a.val :=
  ZMod.val_natCast_of_lt (indexOfWord a).isLt

theorem sub_word_linear_steps {m : ℕ} (hm : 0<m) (a b : Word m) :
    (subWord hm a b).steps=27*m := by
  let t := A1R9.negWord m b.val
  have ⟨hLen,_,hCost⟩ := A1R9.negWord_exact m hm b.val b.property
  change t.steps+(addBits a.val t.result).steps=_
  change t.result.length=m at hLen
  change t.steps=15*m at hCost
  rw [hCost,(addBits_exact a.val t.result (a.property.trans hLen.symm)).2.2,a.property]
  omega

theorem sub_word_residueInt {m : ℕ} (hm : 0<m) (a b : Word m) :
    (bitsValue (subWord hm a b).result.val : ℤ)=residueInt (indexOfWord a) (indexOfWord b) := by
  letI : NeZero (2^m : ℕ) := ⟨by positivity⟩
  rw [←word_read_val,subWord_read]
  have hc : wordRead a-wordRead b =
      (((bitsValue a.val:ℤ)-bitsValue b.val : ℤ) : ZMod (2^m)) := by
    simp [wordRead,asResidue]
  rw [hc,ZMod.val_intCast]
  rfl

def canonicalMachineMatrix (m : ℕ) (hm : 0<m) : Matrix (Fin (2^m)) (Fin (2^m)) ℚ :=
  Matrix.of fun x y=>(bitsValue (subWord hm (wordOfIndex x) (wordOfIndex y)).result.val : ℚ)

theorem canonical_machine_values (m : ℕ) (hm : 0<m) :
    canonicalMachineMatrix m hm=canonicalMatrix (2^m) := by
  ext x y
  have h := sub_word_residueInt hm (wordOfIndex x) (wordOfIndex y)
  simp only [index_of_index_word] at h
  simpa [canonicalMachineMatrix,canonicalMatrix] using congrArg (fun k : ℤ => (k:ℚ)) h

theorem canonical_machine_full_rank (m : ℕ) (hm : 0<m) :
    (integerMatrix (2^m)).rank≤2 ∧ (canonicalMachineMatrix m hm).rank=2^m ∧
      ∀ a b : Word m,(subWord hm a b).steps=27*m := by
  rw [canonical_machine_values]
  exact ⟨(dyadic_rank_amplification m hm).1,(dyadic_rank_amplification m hm).2,
    sub_word_linear_steps hm⟩

#print axioms index_of_index_word
#print axioms word_read_val
#print axioms sub_word_linear_steps
#print axioms sub_word_residueInt
#print axioms canonical_machine_values
#print axioms canonical_machine_full_rank
end Paper5.EscapeE2