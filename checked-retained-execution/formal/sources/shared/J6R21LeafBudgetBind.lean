
import J6R21LeafPrintedStop
import J6R21LeafVertexBound

/-! A leaf receipt usable by the recursive work bound: the uniform
vertex envelope is proved for the actual generated-graph path, not
assumed for arbitrary raw calls. The per-read computational receipt
is still an explicit interface. -/
namespace J6R21Leaf
open scoped Polynomial Classical BigOperators
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6R9Recursive J6R10Repack J6R11Blueprint J6R10Reachable J6R12Blueprint J1PPrinted
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

theorem complete_vertex_list_length {f : ℤ[X]} {ell : ℕ} (H : PhysicalHost f ell)
    (nodes : List (H.Row⊕H.Col)) (hn : nodes.Nodup)
    (hall : ∀ v : H.Row⊕H.Col,v∈nodes) :
    nodes.length=vertexCount H := by
  classical
  letI := H.finiteRow
  letI := H.finiteCol
  have eqset : nodes.toFinset=(Finset.univ : Finset (H.Row⊕H.Col)) :=
    Finset.ext (by intro v; simp [hall v])
  rw [← List.toFinset_card_of_nodup hn,eqset,Finset.card_univ,vertexCount,
    Fintype.card_sum,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]

theorem call_leaf_fee_mono {m u v w : ℕ} (e ell p U : ℕ) (hp : 0<p)
    (hm : m≤u) (hv : v≤w) :
    callLeafFee e ell p m v U hp ≤ callLeafFee e ell p u w U hp := by
  have pow : (2:ℕ)^m≤2^u := Nat.pow_le_pow_right (by decide) hm
  unfold callLeafFee reverseFee
  gcongr

theorem real_reachable_leaf_receipt {f : ℤ[X]} {ell s C : ℕ}
    (cfg : RootBounds s C f)
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (r c : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N sel) (Childs sel) r)]
    (path : NativeReach (Plan sel) r c) (root : Stable s C r)
    (leaf : c.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (hp : 0<c.prec) {fw : List (A1R10.Word c.prec)} (he : 0<fw.length) (hℓ : 0<ell)
    (hPoly : Modulus c.prec hp fw=NativeProbeRing.liftPoly c.prec f)
    (nodes : List (c.host.Row⊕c.host.Col)) (hn : nodes.Nodup)
    (hall : ∀ v : c.host.Row⊕c.host.Col,v∈nodes)
    (query : (c.host.Row⊕c.host.Col)→List Bool→Meter (UVBlock fw ell))
    (U : ℕ)
    (hquery : ∀ (x : Fin c.edges→Bool) v,
      J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (query v (List.ofFn x)).result)=
        (c.host.file v).read hf c.prec
          (assignment c.host.network
            (x∘c.host.edgeOrder c.edges (stable_reachable cfg sel path root).edgeCount) v))
    (hFee : ∀ (x : Fin c.edges→Bool) v, v∈nodes→(query v (List.ofFn x)).steps≤U) :
    let out := leafCompute hp he hℓ c.edges nodes query
    J6R18ChildWrite.castBox hPoly (uvRead hp fw ell out.result) = (sourceBlueprint sel r hf).program.run c ∧
      out.steps≤callLeafFee fw.length ell c.prec ((printedParams (f:=f) (ell:=ell) s).cutoff)
        (vertexCount r.host+4*r.edges) U hp := by
  dsimp only
  have hc := stable_reachable cfg sel path root
  refine ⟨actual_leaf_is_printed_stop sel r c hf leaf hp he hℓ hPoly hc.edgeCount
    nodes hn hall query hquery,?_⟩
  have hn' := complete_vertex_list_length c.host nodes hn hall
  have hv : nodes.length≤vertexCount r.host+4*r.edges := hn'.trans_le (native_vertex_cap cfg sel path root)
  exact (leaf_compute_uniform_fee hp he hℓ c.edges nodes query U hFee).trans
    (call_leaf_fee_mono fw.length ell c.prec U hp leaf hv)

#print axioms complete_vertex_list_length
#print axioms call_leaf_fee_mono
#print axioms real_reachable_leaf_receipt
end J6R21Leaf
