import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.Card

/-! Arbitrary receiver functions after a finite directed message. This is a
semantic one-way information theorem; no polynomial or linear decoder is
assumed. Native probe menus must prove the stated message factorization. -/

namespace FiniteMessage

variable {X Y Z K : Type*} [Fintype Y] [Fintype Z] [DecidableEq Z] [Field K]

def indicator (message : X → Z) : Matrix X Z K :=
  fun x z => if z = message x then 1 else 0

def decoded (message : X → Z) (decode : Z → Y → K) : Matrix X Y K :=
  fun x y => decode (message x) y

omit [Fintype Y] in
theorem message_factorization (message : X → Z) (decode : Z → Y → K) :
    decoded message decode = indicator message * Matrix.of decode := by
  ext x y
  simp [decoded, indicator, Matrix.mul_apply]

theorem arbitrary_decoder_rank (message : X → Z) (decode : Z → Y → K) :
    (decoded message decode).rank ≤ Fintype.card Z := by
  rw [message_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

theorem output_rank_bound (F : Matrix X Y K) (message : X → Z)
    (decode : Z → Y → K) (correct : ∀ x y, F x y = decode (message x) y) :
    F.rank ≤ Fintype.card Z := by
  have he : F = decoded message decode := by
    ext x y
    exact correct x y
  rw [he]
  exact arbitrary_decoder_rank message decode

theorem bit_message_bound (F : Matrix X Y K) (b : ℕ)
    (message : X → (Fin b → Bool)) (decode : (Fin b → Bool) → Y → K)
    (correct : ∀ x y, F x y = decode (message x) y) : F.rank ≤ 2 ^ b := by
  simpa using output_rank_bound F message decode correct

theorem full_rank_forces_bits (F : Matrix X Y K) (m b : ℕ)
    (full : F.rank = 2 ^ m)
    (message : X → (Fin b → Bool)) (decode : (Fin b → Bool) → Y → K)
    (correct : ∀ x y, F x y = decode (message x) y) : 2 ^ m ≤ 2 ^ b := by
  rw [← full]
  exact bit_message_bound F b message decode correct

#print axioms message_factorization
#print axioms arbitrary_decoder_rank
#print axioms output_rank_bound
#print axioms bit_message_bound
#print axioms full_rank_forces_bits

end FiniteMessage
