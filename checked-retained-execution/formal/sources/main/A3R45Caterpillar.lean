import A3R45RealState
import V8PooledRangeResults
import CaterpillarRawEscape

/-! A3 applied to the same original five-copy cubic host as the endpoint
range theorem. Lower bounds for charged novel bit answers and the raw
clause-reading escape concern the very same two-terminal promise. -/
namespace A3R45Caterpillar
open V8PooledRange V8PooledRange.Split A3R45RealState
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

theorem exact_caterpillar_fee {k : ℕ} {E Menu State : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H)
    (menus : Finset Menu) (states : Menu → Finset State)
    (trees : Menu → State → TraceTree ℕ) (B b w T : ℝ) (hw : 0<w)
    (hm : (menus.card:ℝ)≤(2:ℝ)^B)
    (hs : ∀ m∈menus, ((states m).card:ℝ)≤(2:ℝ)^b)
    (ht : ∀ m∈menus, ∀ s∈states m, traceCap (trees m s) T ∧ feasibleRate w (trees m s))
    (correct : endpointRange H p⊆allOutputs menus states trees) :
    ((((Fintype.card (V k):ℝ)-10)/12)-B-b)/w ≤ T := by
  have ne : (endpointRange H p).Nonempty := by
    rw [endpoint_range_agrees]
    exact ⟨_, CaterpillarRange.mem_attained k ((fun _ => false),false)⟩
  have h := exact_A5_real_rate menus states trees (endpointRange H p) B b w T hw ne hm hs ht correct
  apply le_trans ?_ h
  apply div_le_div_of_nonneg_right _ hw.le
  have hr := c6_endpoint_log_range H p
  unfold Real.logb at hr
  linarith only [hr]

theorem identical_raw_update (k : ℕ) (word : Fin k→Bool) :
    CaterpillarRawEscape.run k word = CaterpillarRange.counts k word := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change CaterpillarRawEscape.step (word 0) (CaterpillarRawEscape.run k (fun i => word i.succ)) =
      CaterpillarRange.step (word 0) (CaterpillarRange.counts k (fun i => word i.succ))
    rw [ih]
    rfl

/-- One fixed raw address per switch, with terminal, reads enough to obtain
the count of the same five-copy CNF as in the fee bound. The integer
recurrence's measured operand widths are quadratic, not an oracle fee. -/
theorem raw_switch_escape_same_host {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) (word : Word k) (endpoint : Bool) :
    let R := CaterpillarRawEscape.read k word endpoint
    CaterpillarRawEscape.rawDecoder k R =
        satCount (graph H p) (ports H p) (hostEnabled k word endpoint) ∧
      Fintype.card (CaterpillarRawEscape.RawAddress k) = k+1 ∧
      CaterpillarRawEscape.additionWidths k word ≤ k*(k+1) := by
  dsimp only
  refine ⟨?_, CaterpillarRawEscape.rawAddress_count k,
    CaterpillarRawEscape.quadratic_addition_widths k word⟩
  rw [exact_endpoint]
  simp only [CaterpillarRawEscape.rawDecoder, CaterpillarRawEscape.read,
    CaterpillarRawEscape.table_read, CaterpillarRawEscape.answer, CaterpillarRange.output]
  rw [identical_raw_update]

#print axioms exact_caterpillar_fee
#print axioms identical_raw_update
#print axioms raw_switch_escape_same_host
end A3R45Caterpillar
