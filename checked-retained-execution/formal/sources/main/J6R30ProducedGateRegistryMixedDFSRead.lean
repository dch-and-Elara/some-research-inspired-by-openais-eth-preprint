
import J6R30ProducedGateRegistryDFS
import J6R30ProducedGateRegistryHeterogeneous

/-! All earlier heterogeneous entries remain executable after a genuinely
metered descendant DFS publication. The receiver fetches the same
native birth shape and payload, but the current directory is larger. -/
namespace J6R30ProducedGateRegistry
open scoped Polynomial
open AOracleMachineTime A1R10 J6R21Ancestor

set_option maxHeartbeats 2600000 in
theorem consume_envelope_after_subtree {f : ℤ[X]} {q ell key prec tw bw : ℕ}
    (hf : f.Monic) (hq : 0<q) (hEll : 0<ell) {new : List (A1R10.Word q)}
    (law : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (addr : J6R15ModeCost.Word key) (depth : ℕ) (wires : List WireRead) (bits : List Bool)
    (B : AnyLedger f ell key prec tw bw)
    (F : Forest (Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (Envelope f ell prec)))
    (h : JobsReady B F.inOrder) (old : ∀ j∈F.inOrder,j.identifier≠addr) :
    let read := consumeEnvelope hf hq hEll law addr depth wires bits B
    consumeEnvelope hf hq hEll law addr depth wires bits (publishDFS B F).result.1 =
      ⟨read.result,read.steps+F.inOrder.length*refHeadFee key⟩ := by
  have stored := dfs_old_capsule_receipt B F h addr old
  unfold consumeEnvelope
  dsimp only
  rw [stored]
  dsimp only
  cases hit : (locate addr B.records).result <;> dsimp only
  all_goals congr 1; omega

#print axioms consume_envelope_after_subtree
end J6R30ProducedGateRegistry

