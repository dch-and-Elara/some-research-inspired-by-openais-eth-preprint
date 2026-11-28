import J9R19CompiledBitsAggregate

/-! J7's paid rational postprocessing: divide by the integer baseline,
subtract the public rational background (its integer numerator with the
same denominator), and solve the literal Vandermonde system with the
already verified prefix/stencil machine. No new arithmetic cost model. -/
namespace J7R43Literal
open scoped BigOperators
open J9R19CompiledBits NativeMomentReconstruction
set_option autoImplicit false

def literalDecoderInput {n : ℕ} (base : ℤ) (bg obs : Fin n→ℤ) :
    Fin n→PhysicalFractions :=
  fun j => ⟨⟨obs j,1⟩,⟨base,1⟩,⟨bg j,base⟩⟩

theorem literal_decoder_machine_correct {n : ℕ}
    (coord : Fin n→ℤ) (base : ℤ) (bg obs : Fin n→ℤ) (j : Fin n)
    (coordinates_injective : Function.Injective coord) (base_ne : base≠0) :
    (recoverRun coord (literalDecoderInput base bg obs) j).answer =
      decodeBits (fun k => (coord k:ℚ)) (fun _ => (base:ℚ))
        (fun k => (bg k:ℚ)/(base:ℚ)) (fun k => (obs k:ℚ)) j := by
  have hx : Function.Injective (fun k => (coord k : ℚ)) :=
    fun _ _ eq => coordinates_injective (Int.cast_injective eq)
  rw [recoverRun_exact _ _ _ coordinates_injective]
  · simpa only [literalDecoderInput,Fraction.value,Int.cast_one,div_one] using
      congrFun (J9R18Compiled.stencilDecodeBits_exact (fun k => (coord k:ℚ)) (fun _ => (base:ℚ))
        (fun k => (bg k:ℚ)/(base:ℚ)) (fun k => (obs k:ℚ)) hx) j
  · intro k
    exact ⟨one_ne_zero,base_ne,base_ne⟩

theorem literal_decoder_machine_work {n : ℕ}
    (coord : Fin n→ℤ) (base : ℤ) (bg obs : Fin n→ℤ) (j : Fin n) :
    (recoverRun coord (literalDecoderInput base bg obs) j).work ≤ n*(n+1)+14*n+2 :=
  recoverRun_work _ _ _

theorem literal_decoder_machine_words {n a w : ℕ}
    (coord : Fin n→ℤ) (base : ℤ) (bg obs : Fin n→ℤ) (j : Fin n)
    (hc : ∀ k, Fits a (coord k)) (hb : Fits w base)
    (hg : ∀ k, Fits w (bg k)) (ho : ∀ k, Fits w (obs k)) :
    let N := normalTape (literalDecoderInput base bg obs)
    let st := evaluateStencil coord (fun k => storedFraction N k.val) j
    (∀ s∈N, ∀ x∈s.words, Fits (3*w+1) x) ∧
    st.result.fits (decoderBudget n a w) ∧
    (∀ x∈st.words, Fits (decoderBudget n a w) x) := by
  apply decoder_words_bound _ _ _ hc
  have hone : Fits w 1 := Fits.one w
  intro k
  exact ⟨⟨ho k,hone⟩,⟨hb,hone⟩,⟨hg k,hb⟩⟩

#print axioms literal_decoder_machine_correct
#print axioms literal_decoder_machine_work
#print axioms literal_decoder_machine_words
end J7R43Literal
