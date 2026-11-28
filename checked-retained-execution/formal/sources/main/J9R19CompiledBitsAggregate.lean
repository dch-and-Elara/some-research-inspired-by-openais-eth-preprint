
import J9R19CompiledBitsDecode
import J9R19CompiledBitsPhysicalBudget
import J9R19CompiledBitsPrimitives

/-! Aggregate decoder work and uniform native physical word width. The
acquisition polynomial accounts for the sizes of the actual fractions,
and the postprocessing work bound does not count the separately
printed raw registers as if the shortcut evaluated them. -/
namespace J9R19CompiledBits
open scoped BigOperators Classical
open J8Physical J8EndToEnd J8J9Grouped LiteralPortCompiler
set_option linter.unusedSectionVars false

def decoderBudget (n a b : ℕ) : ℕ :=
  let W := (a+1)*n
  let B := W+(3*b+1)
  B+(B+1)*n+W

theorem decoder_words_bound {n a b : ℕ} (coord : Fin n→ℤ) (q : Fin n→PhysicalFractions)
    (i : Fin n) (hf : ∀ j, Fits a (coord j))
    (hq : ∀ j, (q j).first.fits b ∧ (q j).scale.fits b ∧ (q j).background.fits b) :
    let N := normalTape q
    let st := evaluateStencil coord (fun j => storedFraction N j.val) i
    (∀ s∈N, ∀ x∈s.words, Fits (3*b+1) x) ∧
    st.result.fits (decoderBudget n a b) ∧ (∀ x∈st.words, Fits (decoderBudget n a b) x) := by
  let N := normalTape q
  have hs (j : Fin n) : (storedFraction N j.val).fits (3*b+1) := by
    rw [stored_normal]
    exact (normalizeRun_fits _ _ _ (hq j).1 (hq j).2.1 (hq j).2.2).1
  refine ⟨?_,?_⟩
  · intro s hs' x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs'
    exact (normalizeRun_fits _ _ _ (hq j).1 (hq j).2.1 (hq j).2.2).2 x hx
  · exact evaluateStencil_word_width coord _ i hf hs

theorem acquisitionBudget_order_mono (L v M g : ℕ) {b c : ℕ} (h : b≤c) :
    acquisitionBudget L v M g b≤acquisitionBudget L v M g c := by
  unfold acquisitionBudget clearBudget slopeBudget momentBudget
  gcongr

noncomputable section
variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

theorem physicalDecoder_words (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (F : OldTables d) (a : S) (sign : S→Bool) (i : Fin (Fintype.card (PinTile d a)))
    (sparse : ∀ v, Fintype.card (P v)≤3) :
    let B := acquisitionBudget L (Fintype.card V) (Fintype.card (Wire R)) (Fintype.card G) L
    let N := normalTape (fun j => physicalFractions d e he F a j sign)
    let n := Fintype.card (PinTile d a)
    let st := evaluateStencil (coordinateInt d a) (fun j => storedFraction N j.val) i
    (∀ s∈N, ∀ x∈s.words, Fits (3*B+1) x) ∧
    st.result.fits (decoderBudget n L B) ∧ (∀ x∈st.words, Fits (decoderBudget n L B) x) := by
  apply decoder_words_bound _ _ _ (coordinateInt_fits d a)
  intro j
  have h (j : Fin (Fintype.card (PinTile d a))) : j.val≤L := by
    have hc := pins_per_tile d a he
    have hj := j.isLt
    omega
  have w := acquisitionBudget_order_mono L (Fintype.card V) (Fintype.card (Wire R))
    (Fintype.card G) (h j)
  have fit := physicalFractions_width d e he hL F a j sign sparse
  exact ⟨⟨fit.1.1.mono w,fit.1.2.mono w⟩,
    ⟨fit.2.1.1.mono w,fit.2.1.2.mono w⟩,⟨fit.2.2.1.mono w,fit.2.2.2.mono w⟩⟩

/-- All decoder sites, counting one signed-numerator equality each. Input
fractions can be materialized once per order, as in the R18 plan. This
counts only recovery arithmetic after that acquisition. -/
def allRecoveryWork (e : EndpointSeating d) (he : Even L) (F : OldTables d) (sign : S→Bool) : ℕ :=
  ∑ j : J9R17AllPins.Orders d,
    (recoverTileRun d e he F (J9R17AllPins.anchor d j.1) sign j.2).work

theorem allRecoveryWork_bound (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (sign : S→Bool) :
    allRecoveryWork d e he F sign≤Fintype.card S*(L*(L+1)+14*L+2) := by
  let B := L*(L+1)+14*L+2
  have hb (j : J9R17AllPins.Orders d) :
      (recoverTileRun d e he F (J9R17AllPins.anchor d j.1) sign j.2).work≤B := by
    refine (recoverRun_work _ _ _).trans ?_
    have hc : Fintype.card (PinTile d (J9R17AllPins.anchor d j.1))≤L := by
      have h := pins_per_tile d (J9R17AllPins.anchor d j.1) he
      omega
    dsimp only [B]
    gcongr
  unfold allRecoveryWork
  calc
    _ ≤ ∑ _j : J9R17AllPins.Orders d, B := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,
        Fintype.card_congr (J9R17AllPins.orderPin d)]

#print axioms decoder_words_bound
#print axioms acquisitionBudget_order_mono
#print axioms physicalDecoder_words
#print axioms allRecoveryWork_bound

end
end J9R19CompiledBits
