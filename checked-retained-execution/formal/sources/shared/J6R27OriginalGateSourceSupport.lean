
import J6R27OriginalGateDense

/-! On the actual paid emitter's accepted event, the sparse message
and the corresponding complete multiplicity record agree. The theorem
does not assume an arbitrary table of exponent values or grant free
selection of a particular event from a whole batch. -/
namespace J6R27OriginalGate
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply

theorem actual_batch_sparse_receipt {q : ℕ} (a : ℕ) (T : RawTape q) (D : RawValid T)
    (distinct : T.modes.Nodup)
    (fits : ∀ m∈T.modes,m.key.1.length≤6*a ∧ m.key.2.length≤6*a)
    (es : List (Word q))
    (occurs : es∈(emitBatch a T D.posWidth D.posPrec D.posWeights).result.vectors) :
    let B := (emitBatch a T D.posWidth D.posPrec D.posWeights).result
    let sp := supportSpec T.modes es
    some sp∈B.support ∧
      (densify T.modes sp).result=some es ∧
      (densify T.modes sp).steps≤4+T.modes.length*denseRecordFee a q := by
  let B := (emitBatch a T D.posWidth D.posPrec D.posWeights).result
  obtain ⟨_,read,sparse,_⟩ := emit_batch_exact a T D.posWidth D.posPrec D.posWeights D.sameLength
  have hPos (z : ℕ) (hz : z∈T.weights.map Word.val) : 0<z := by
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact D.posWeights w hw
  have hS : es.map Word.val∈strictTuples (T.weights.map Word.val) T.precision.val := by
    rw [←read]
    exact List.mem_map_of_mem occurs
  have L : T.modes.length=es.length := by
    have E := ((strictTuples_exact _ _ hPos).2 _ |>.mp hS).1
    simpa only [List.length_map,D.sameLength] using E.symm
  refine ⟨?_,actual_sparse_to_dense T.modes es L distinct,densify_cost a T.modes _ fits⟩
  change some (supportSpec T.modes es)∈B.support
  rw [sparse]
  exact List.mem_map_of_mem occurs

theorem source_key_widths {a pages tiles p q : ℕ} (i : Fin a) (x : PacketMode i pages tiles p) :
    (encodeMode (q:=q) i x).key.1.length=6*a ∧ (encodeMode (q:=q) i x).key.2.length=6*a := by
  simp only [encodeMode,J6R14LayoutCost.wordCell,J6R14LayoutCost.coordinateLabel_len,and_self]

#print axioms actual_batch_sparse_receipt
#print axioms source_key_widths
end J6R27OriginalGate

