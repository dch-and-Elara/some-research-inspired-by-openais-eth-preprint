import J6R68CanonicalRootWriterDispatch
import J6R62LeafPrepBounds

/-! An upper bound for the actual framed root writer's operations. The
input record is already present; the bound pays its local copy, syntax
dispatch, frame scan, and wire or Gate seek, plus the one gather cell. -/
namespace J6R68CanonicalRootWriter
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R36ChildFramedRoute
open J6R53OldOwner J6R53TerminalGate J6R52Terminal J6R62Leaf

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 9500000

def rootOwnerRowCap (w W own key prec page E U b d : ℕ) : ℕ :=
  (3*own+1)+ownerDataCap w key prec page d+
    max (savedGateCap w W own E U b d) (max (freshPageCap W key page E U) 3)+12

theorem root_owner_row_copies_and_seeks_under_sizes
    {W w own key prec page E U : ℕ}
    (b d : ℕ) (book : List (Word W)) (nb : book.length≤E)
    (frames : List (FramedEdge W own key prec page)) (nf : frames.length≤E)
    (forms : FramesFit frames U) (row : RefRow own (OwnerData w key prec page))
    (gates : ∀ g,row.payload.gateCode=some g → GateFit d g) :
    (writeRootOwner b book frames row).steps+7≤rootOwnerRowCap w W own key prec page E U b d := by
  have hcopy := actual_gate_roster_payload_cap row.payload gates
  have hop : (decideRootSource b book frames row.address row.payload).steps≤
      max (savedGateCap w W own E U b d) (max (freshPageCap W key page E U) 3) := by
    unfold decideRootSource
    cases g : row.payload.gateCode with
    | some op =>
      dsimp only
      exact (same_owner_gate_compilation_fee frames forms nf book nb row.address b d op
        (gates op g)).trans (le_max_left _ _)
    | none =>
      cases k : row.payload.origin.pageKey with
      | none =>
        dsimp only
        exact (le_max_right (freshPageCap W key page E U) 3).trans (le_max_right _ _)
      | some pg =>
        dsimp only
        exact (actual_fresh_page_compile_cap row.payload.origin.stamp.creator book nb frames nf
          forms pg).trans ((le_max_left _ _).trans (le_max_right _ _))
  rw [root_owner_write_exact_cost]
  dsimp only
  unfold rootOwnerRowCap
  omega

theorem root_owner_roster_cost_by_actual_length
    {W w own key prec page E U : ℕ}
    (b d : ℕ) (book : List (Word W)) (nb : book.length≤E)
    (frames : List (FramedEdge W own key prec page)) (nf : frames.length≤E)
    (forms : FramesFit frames U) (rows : RawRoster own w key prec page)
    (gates : ∀ row∈rows,∀ g,row.payload.gateCode=some g → GateFit d g) :
    (rows.map (fun row=>(writeRootOwner b book frames row).steps+7)).sum
      ≤rows.length*rootOwnerRowCap w W own key prec page E U b d :=
  sum_map_cap rows _ _ (fun row mem=>
    root_owner_row_copies_and_seeks_under_sizes b d book nb frames nf forms row (gates row mem))

#print axioms root_owner_row_copies_and_seeks_under_sizes
#print axioms root_owner_roster_cost_by_actual_length
end J6R68CanonicalRootWriter
