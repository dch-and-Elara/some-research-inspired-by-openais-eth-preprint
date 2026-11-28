import J7FullWordLaw

/-! # Printed source word convention and cell count -/

open scoped BigOperators Classical
open J7SourceConditioning J7FullWordLaw

namespace J7FullWordPrinted
noncomputable section

/-- Printing the retained coordinate separately loses no coordinates.
Source coordinate zero is the head; the remaining coordinates are the
tail. -/
def wordEquiv (A : Type*) (t : ℕ) : (A × (Fin t → A)) ≃ (Fin (t+1) → A) where
  toFun w := Fin.cons w.1 w.2
  invFun w := (w 0,Fin.tail w)
  left_inv := by rintro ⟨a,w⟩; simp
  right_inv := by intro w; exact Fin.cons_self_tail w

theorem wordEquiv_retained {A : Type*} {t : ℕ} (w : A × (Fin t → A)) :
    wordEquiv A t w 0 = w.1 := by simp [wordEquiv]

theorem wordEquiv_rest {A : Type*} {t : ℕ} (w : A × (Fin t → A)) (i : Fin t) :
    wordEquiv A t w i.succ = w.2 i := by simp [wordEquiv]

/-- Uniform tail words are exactly the product of independently uniform
source symbols in every coordinate other than the retained one. -/
theorem tail_word_product {A : Type*} [Fintype A] (t : ℕ)
    (w : Fin t → A) :
    uniform (Fin t → A) w = productWeight (fun _ => uniform A) w := by
  simp [uniform, productWeight, Finset.prod_const]

/-- At the printed alphabet r=64 and a=2u, D=r^(2a) is L^12. -/
theorem printed_cell_count (u : ℕ) :
    (64 : ℕ)^(2*(2*u)) = (2^(2*u))^12 := by
  rw [show (64 : ℕ) = 2^6 by decide, ← pow_mul, ← pow_mul]
  congr 1
  omega

#print axioms wordEquiv
#print axioms wordEquiv_retained
#print axioms wordEquiv_rest
#print axioms tail_word_product
#print axioms printed_cell_count

end
end J7FullWordPrinted
