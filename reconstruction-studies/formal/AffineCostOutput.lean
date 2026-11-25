import AffineCostFraction

namespace AffineCost.Bit

/-- Each bit is preceded by a true cell, and the frame ends in a false cell. -/
def emitWord : Word → Run Word
  | [] => ⟨[false],4⟩
  | x :: xs =>
    let r := emitWord xs
    ⟨true :: x :: r.value, 4+r.steps⟩

theorem emitWord_length (xs : Word) : (emitWord xs).value.length = 2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [emitWord, ih, Nat.mul_add]

theorem emitWord_steps (xs : Word) : (emitWord xs).steps = 4*(xs.length+1) := by
  induction xs <;> simp [emitWord, *, Nat.mul_add, Nat.add_comm]

/-- The output stream stores the two signed integers as four self-delimiting
binary magnitude strings. An unreduced nonzero denominator is sufficient. -/
def emitFraction (a : Fraction) : Run Word :=
  let np := emitWord a.num.plus
  let nn := emitWord a.num.minus
  let dp := emitWord a.den.plus
  let dn := emitWord a.den.minus
  ⟨np.value ++ nn.value ++ dp.value ++ dn.value,
    8 + np.steps + nn.steps + dp.steps + dn.steps +
      (np.value.length+nn.value.length+dp.value.length)⟩

theorem emitFraction_steps (a : Fraction) : (emitFraction a).steps ≤ 32*(a.size+1) := by
  have h₀ := Fraction.num_size a
  have h₁ := Fraction.den_size a
  have h₂ : a.num.plus.length ≤ a.num.size := le_max_left _ _
  have h₃ : a.num.minus.length ≤ a.num.size := le_max_right _ _
  have h₄ : a.den.plus.length ≤ a.den.size := le_max_left _ _
  have h₅ : a.den.minus.length ≤ a.den.size := le_max_right _ _
  simp only [emitFraction, emitWord_steps, emitWord_length]
  omega

/-- Parsing one frame returns its bit string and the remaining stream. -/
def readWord : Word → Option (Word × Word)
  | false :: xs => some ([], xs)
  | true :: b :: xs => (readWord xs).map fun p => (b :: p.1, p.2)
  | _ => none

theorem readWord_emit (xs rest : Word) :
    readWord ((emitWord xs).value ++ rest) = some (xs, rest) := by
  induction xs <;> simp [emitWord, readWord, *]

def readFraction (s : Word) : Option (Fraction × Word) := do
  let (np,s) ← readWord s
  let (nn,s) ← readWord s
  let (dp,s) ← readWord s
  let (dn,s) ← readWord s
  return (⟨⟨np,nn⟩,⟨dp,dn⟩⟩,s)

theorem readFraction_emit (a : Fraction) (rest : Word) :
    readFraction ((emitFraction a).value ++ rest) = some (a,rest) := by
  cases a
  simp [readFraction, emitFraction, List.append_assoc, readWord_emit]

@[simp] theorem readFraction_emitted (a : Fraction) :
    readFraction (emitFraction a).value = some (a,[]) := by
  simpa only [List.append_nil] using readFraction_emit a []

end AffineCost.Bit
