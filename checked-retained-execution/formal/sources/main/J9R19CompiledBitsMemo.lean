
import J9R19CompiledBitsAggregate

/-! Memoization of the actual compiled fraction tape, not of raw
recursive receipts. It is built once per original tile-and-order
address. The checked recoverer may then visit a stored value as often
as needed without re-evaluating an old truth table. -/
namespace J9R19CompiledBits
open scoped BigOperators Classical
open J8Physical J8EndToEnd J8J9Grouped LiteralPortCompiler
set_option linter.unusedSectionVars false
noncomputable section

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

def gatherFractions {N : ℕ} (idx : Fin N ≃ J9R17AllPins.Orders d)
    (e : EndpointSeating d) (he : Even L) (F : OldTables d) (sign : S→Bool) :
    List PhysicalFractions :=
  List.ofFn (fun j =>
    let w := idx j
    physicalFractions d e he F (J9R17AllPins.anchor d w.1) w.2 sign)

theorem gatherFractions_count {N : ℕ} (idx : Fin N ≃ J9R17AllPins.Orders d)
    (e : EndpointSeating d) (he : Even L) (F : OldTables d) (sign : S→Bool) :
    (gatherFractions d idx e he F sign).length=Fintype.card S := by
  unfold gatherFractions
  rw [List.length_ofFn,← Fintype.card_fin N,Fintype.card_congr idx,
    Fintype.card_congr (J9R17AllPins.orderPin d)]

def readMemo {N : ℕ} (data : List PhysicalFractions) (idx : Fin N ≃ J9R17AllPins.Orders d)
    (w : J9R17AllPins.Orders d) : PhysicalFractions :=
  data[(idx.symm w).val]?.getD ⟨⟨0,1⟩,⟨0,1⟩,⟨0,1⟩⟩

theorem readMemo_exact {N : ℕ} (idx : Fin N ≃ J9R17AllPins.Orders d)
    (e : EndpointSeating d) (he : Even L) (F : OldTables d) (sign : S→Bool)
    (w : J9R17AllPins.Orders d) :
    readMemo d (gatherFractions d idx e he F sign) idx w =
      physicalFractions d e he F (J9R17AllPins.anchor d w.1) w.2 sign := by
  simp [readMemo,gatherFractions,(idx.symm w).isLt]
  exact congrArg (fun k : J9R17AllPins.Orders d =>
    physicalFractions d e he F (J9R17AllPins.anchor d k.1) k.2 sign) (idx.apply_symm_apply w)

def restoreAllMemo {N : ℕ} (idx : Fin N ≃ J9R17AllPins.Orders d)
    (data : List PhysicalFractions) (s : S) : RecoveryRun :=
  let w := (J9R17AllPins.orderPin d).symm s
  recoverRun (coordinateInt d (J9R17AllPins.anchor d w.1))
    (fun j => readMemo d data idx ⟨w.1,j⟩) w.2

theorem restoreAllMemo_matches {N : ℕ} (idx : Fin N ≃ J9R17AllPins.Orders d)
    (e : EndpointSeating d) (he : Even L) (F : OldTables d) (sign : S→Bool) (s : S) :
    let w := (J9R17AllPins.orderPin d).symm s
    restoreAllMemo d idx (gatherFractions d idx e he F sign) s =
      recoverTileRun d e he F (J9R17AllPins.anchor d w.1) sign w.2 := by
  simp only [restoreAllMemo,recoverTileRun,readMemo_exact d idx e he F sign]

theorem memo_compiled_all_pins {N : ℕ} (idx : Fin N ≃ J9R17AllPins.Orders d)
    (e : EndpointSeating d) (he : Even L) (hL : 2<L) (F : OldTables d) (sign : S→Bool)
    (off : ∀ a, d.rowLabel (pinWire d a).1≠d.pinLabel a)
    (sat : ∀ g v, ∃ z, satisfied (F g v) z=true) :
    (fun s => (restoreAllMemo d idx (gatherFractions d idx e he F sign) s).answer)=sign := by
  simp only [restoreAllMemo_matches d idx e he F sign]
  exact recover_all_pins_integer d e he hL F sign off sat

#print axioms gatherFractions_count
#print axioms readMemo_exact
#print axioms restoreAllMemo_matches
#print axioms memo_compiled_all_pins

end
end J9R19CompiledBits
