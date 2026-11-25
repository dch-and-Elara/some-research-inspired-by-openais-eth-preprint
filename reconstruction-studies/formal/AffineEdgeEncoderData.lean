import AffineEdgeCenter
import Mathlib.Data.Matrix.Basic

open scoped BigOperators Polynomial

namespace AffineEdge

noncomputable section

variable {q : ℕ} {F : Type*} [Field F]

abbrev EncoderRow (q : ℕ) := Fin q ⊕ (Fin ((q+1)/2) ⊕ Bool)

def bucket (t : Fin q) : Fin ((q+1)/2) := ⟨t.val/2, by have := t.isLt; omega⟩

def bitScalar {R : Type*} [Zero R] [One R] (b : Bool) : R := if b then 1 else 0

def parity (a : Bits q) : Bool :=
  decide ((∑ t, bitScalar (R := ℕ) (a t)) % 2 = 1)

theorem parity_flip (a : Bits q) (t : Fin q) : parity (flip t a) ≠ parity a := by
  unfold parity
  have h (b : Bits q) := Finset.sum_erase_add (s := Finset.univ)
    (fun j => bitScalar (R := ℕ) (b j)) (Finset.mem_univ t)
  have he : (∑ j ∈ Finset.univ.erase t, bitScalar (R := ℕ) (flip t a j)) =
      ∑ j ∈ Finset.univ.erase t, bitScalar (R := ℕ) (a j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [flip_other (Finset.ne_of_mem_erase hj)]
  have h1 := h a
  have h2 := h (flip t a)
  rw [he] at h2
  simp only [flip_same] at h2
  cases hk : a t <;> simp [bitScalar, hk] at h1 h2 ⊢ <;> omega

def encoderColumn (a : Bits q) : Kind q → EncoderRow q → F
  | none, .inr (.inr b) => if b = parity a then 1 else 0
  | some s, .inl t => if t = s then 1 else 0
  | some s, .inr (.inl b) => if b = bucket s then bitScalar (a s) else 0
  | _, _ => 0

private def hardEmbedding (q : ℕ) : Bits q × Kind q ↪ Word q where
  toFun p := hardWord p.1 p.2
  inj' := by
    rintro ⟨a,k⟩ ⟨b,l⟩ h
    have he : a = b := congrArg Prod.fst h
    subst b
    exact congrArg (Prod.mk a) (step_injective _ (congrArg Prod.snd h))

/-- The paper's binary-valued encoder on the full array of physical words. -/
def binaryEncoder (q : ℕ) : Matrix (EncoderRow q) (Word q) F :=
  fun j => Function.extend (hardEmbedding q) (fun p => encoderColumn p.1 p.2 j) 0

@[simp] theorem binaryEncoder_hardWord (a : Bits q) (k : Kind q) (j : EncoderRow q) :
    binaryEncoder (F := F) q j (hardWord a k) = encoderColumn a k j :=
  (hardEmbedding q).injective.extend_apply _ _ (a,k)

theorem binaryEncoder_zero_other (v : Word q) (hv : ¬∃ k, hardWord v.1 k = v)
    (j : EncoderRow q) : binaryEncoder (F := F) q j v = 0 := by
  unfold binaryEncoder
  apply Function.extend_apply'
  rintro ⟨⟨a,k⟩,h⟩
  have ha : a = v.1 := congrArg Prod.fst h
  subst a
  exact hv ⟨k,h⟩

theorem binaryEncoder_binary (j : EncoderRow q) (v : Word q) :
    binaryEncoder (F := F) q j v = 0 ∨ binaryEncoder (F := F) q j v = 1 := by
  by_cases h : ∃ k, hardWord v.1 k = v
  · obtain ⟨k, hk⟩ := h
    have he : binaryEncoder (F := F) q j v = encoderColumn v.1 k j := hk ▸
      binaryEncoder_hardWord v.1 k j
    rw [he]
    rcases j with t | b | b
    · cases k with
      | none => exact Or.inl rfl
      | some s => by_cases h : t = s <;> simp [encoderColumn,h]
    · cases k with
      | none => exact Or.inl rfl
      | some s =>
        by_cases h : b = bucket s
        · cases hb : v.1 s <;> simp [encoderColumn,bitScalar,h,hb]
        · simp [encoderColumn,h]
    · cases k with
      | none => by_cases h : b = parity v.1 <;> simp [encoderColumn,h]
      | some _ => exact Or.inl rfl
  · exact Or.inl (binaryEncoder_zero_other v h j)

end
end AffineEdge
