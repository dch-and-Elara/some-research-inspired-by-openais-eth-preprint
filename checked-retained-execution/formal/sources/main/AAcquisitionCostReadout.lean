import AAcquisitionCostDivision
import AAcquisitionCostTape

/-! A4's exact bit-stream readout on the certified padded layout.
The actual register reply is supplied in unsigned binary; neither this
readout nor its complexity assumes a cheap way to obtain that reply. -/

namespace AAcquisitionCost
open Acquisition

theorem assembledCover_readout {E V₂ V₃ P : Type*} {u c L M p : ℕ}
    [Fintype E] [DecidableEq E] [Fintype V₂] [DecidableEq V₂]
    [Fintype V₃] [DecidableEq V₃] [DecidableEq P]
    (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E)
    (cols : CoverOccurrences V₂ V₃ (Fin u) ≃ CoverCol E V₃ (Fin c))
    (seat : (CoverOccurrences V₂ V₃ (Fin u) × Bool) ≃ P × Fin L) (hL : 0 < L)
    (planted : ∀ (r : CoverRow V₂ V₃ (Fin u)) (j : CoverPort r),
      (wirePred seat (⟨r,j⟩,true)).map (cols ∘ Prod.fst) =
        coverSources at₂ at₃ (compiledStray seat cols) r j)
    (even : Even (Fintype.card V₃)) (hE : 2*Fintype.card E ≤ M)
    (hC : 2*c ≤ M) (hp : 2*M < p) (reply : List Bool)
    (observation : feedValue reply 0 =
      (literalMeshRegister (coverTables (K := ZMod (2^p))) cols L (packetOf seat)
        (positionOf seat)).val) :
    wordNat (binaryDivide (binaryNormalizer (compiledStray seat cols)) reply) =
      coverCount at₂ at₃ := by
  rw [normalizer_divide_exact _ (compiledStray_load_le seat cols),observation]
  exact seatedCover_decode at₂ at₃ cols seat hL planted even hE (by simpa using hC) hp

/-- Count the certified acquisition-independent stream stages.  The
first term is the explicitly supplied tape, not a pointer-size address
for an implicitly represented, exponentially large layout. -/
def coverReadoutSize (layoutRows width u c p : ℕ) : ℕ :=
  explicitAddressBits layoutRows width + explicitNormalizerSize u c p

theorem coverReadout_schedule_poly {u c : ℕ}
    (tap : Fin u → Option (Fin c)) (physicalTape : List (List Bool)) (width : ℕ)
    (wellSized : ∀ w ∈ physicalTape, w.length ≤ width) (reply : List Bool) :
    (tapeTrace none physicalTape).length + factorScanCost tap +
      productSchedule (factorTape tap) 1 + divisionSchedule reply (binaryNormalizer tap)
      ≤ 33*(coverReadoutSize physicalTape.length width u c reply.length)^3 := by
  let T := explicitAddressBits physicalTape.length width
  let Z := explicitNormalizerSize u c reply.length
  let S := T+Z
  have ht := tapeTrace_linear_bits none physicalTape width (by simp) wellSized
  have hz := normalizer_schedule_poly tap reply.length
  have hd := divisionSchedule_quadratic tap reply
  have hs : 1 ≤ S := by dsimp [S,T,Z,explicitAddressBits,explicitNormalizerSize]; omega
  have hq : reply.length+c+1 ≤ S := by dsimp [S,Z,explicitNormalizerSize]; omega
  have h0 : T ≤ S := by dsimp [S]; omega
  have h1 : Z ≤ S := by dsimp [S]; omega
  have h2 : (reply.length+c+1)^2 ≤ S^2 := Nat.pow_le_pow_left hq _
  have h3 : S^2 ≤ S^3 := Nat.pow_le_pow_right hs (by decide)
  have h4 : S ≤ S^3 := by
    simpa using Nat.pow_le_pow_right hs (show 1 ≤ 3 by decide)
  have h5 : Z^3 ≤ S^3 := Nat.pow_le_pow_left h1 _
  change (tapeTrace none physicalTape).length ≤ 2*T at ht
  change factorScanCost tap + productSchedule (factorTape tap) 1 ≤ 18*Z^3 at hz
  have hb1 := ht.trans (Nat.mul_le_mul_left 2 (h0.trans h4))
  have hb2 := hz.trans (Nat.mul_le_mul_left 18 h5)
  have hb3 := hd.trans (Nat.mul_le_mul_left 13 (h2.trans h3))
  change _ ≤ 33*S^3
  omega

#print axioms assembledCover_readout
#print axioms coverReadout_schedule_poly

end AAcquisitionCost
