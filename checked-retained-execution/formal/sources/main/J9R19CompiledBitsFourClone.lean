
import J9R19CompiledBitsMemo

/-! One final theorem on the original degree-three four-clone port atlas.
The small OLD scope is derived from source incidences, not supplied as
a separate oracle hypothesis. This joined statement keeps arithmetic
work, literal table visits, and output width as distinct assertions. -/
namespace J9R19CompiledBits
open scoped Classical BigOperators
open J8Physical J8EndToEnd J8J9Grouped LiteralPortCompiler
open J7PrintedParamsGraph J7ToJ8Incidence
noncomputable section
set_option linter.unusedSectionVars false

theorem fourClone_integer_certificate
    {Pair H Packet R : Type*} [Fintype Pair] [Fintype H] [Fintype Packet] [Fintype R] {L n : ℕ}
    (ends : H×Bool ≃ J7SourceLabels.Pin Pair×Fin 3)
    (d : Layout Packet R (J7SourceLabels.Pin Pair)
      (J7SourceLabels.OrdinaryColumn Pair (OldNonPrivate Pair H))
      (Fin 64) (Ports (column ends cycle)) L)
    (idx : Fin n ≃ J9R17AllPins.Orders d)
    (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (F : OldTables d) (sign : J7SourceLabels.Pin Pair→Bool)
    (off : ∀ a, d.rowLabel (pinWire d a).1≠d.pinLabel a)
    (sat : ∀ g v, ∃ z, satisfied (F g v) z=true) :
    let N := Fintype.card (J7SourceLabels.Pin Pair)
    let M := Fintype.card (Wire R)
    let V := Fintype.card (J7SourceLabels.OrdinaryColumn Pair (OldNonPrivate Pair H))
    let data := gatherFractions d idx e he F sign
    (fun s => (restoreAllMemo d idx data s).answer)=sign ∧
    data.length=N ∧
    J9R18Compiled.compiledVisits d≤16*N*(65+2*M)*M ∧
    allRecoveryWork d e he F sign≤N*(L*(L+1)+14*L+2) ∧
    (∀ a (i : Fin (Fintype.card (PinTile d a))),
      let B := acquisitionBudget L V M (Fintype.card (Fin 64)) L
      let N := normalTape (fun j => physicalFractions d e he F a j sign)
      let width := decoderBudget (Fintype.card (PinTile d a)) L B
      let st := evaluateStencil (coordinateInt d a) (fun j => storedFraction N j.val) i
      (∀ s∈N, ∀ x∈s.words, Fits (3*B+1) x) ∧
      st.result.fits width ∧ (∀ x∈st.words, Fits width x)) := by
  refine ⟨memo_compiled_all_pins d idx e he hL F sign off sat,
    gatherFractions_count d idx e he F sign,J9R18Compiled.fourClone_compiledVisits_bound ends d,
    allRecoveryWork_bound d e he F sign,?_⟩
  intro a i
  apply physicalDecoder_words d e he hL F a sign i
  intro v
  rw [← Nat.card_eq_fintype_card]
  exact J9R18Compiled.fourClone_port_count ends v

#print axioms fourClone_integer_certificate

end
end J9R19CompiledBits
