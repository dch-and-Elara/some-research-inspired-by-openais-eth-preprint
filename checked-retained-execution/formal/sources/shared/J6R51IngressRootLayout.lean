import J6R51IngressGreedy
import J6R51IngressFreshSemantics
import J6R51IngressFreshInputOrder
import J6R30GeneratedRootLayoutReceipt

/-! The fresh legal source graph is an actual input to the printed
root padding and stable seat compiler. Its compact literal bytes,
rather than any earlier frozen R41 file, are the input to this
separate source chart. The generic greedy option is proven separately. -/
namespace J6R51Ingress
open scoped Classical Polynomial
open Std.Sat J7R9Compiler J7R9Subdivision J7R10Plant J6OrientedHostEval
open J6R49RootIngress J6R50RootIngress J6R30GeneratedRootLayout J6Mesh
open J6R24LegalLayout J6R28GeneratedRootFrame J6R26StablePreparedRoot J6R14LayoutCost
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 15600000
noncomputable section

theorem fresh_guard_allOccur {V : Type*} [DecidableEq V] [Nonempty V]
    (F : CNF V) (xs : List V) (all : ∀ v,v∈xs) :
    AllOccur (guardedInOrder F xs) := by
  have h (v : V) : guardSafety v∈guardedInOrder F xs :=
    List.mem_append_right _ (List.mem_map_of_mem (all v))
  intro q
  apply (variable_position_iff _ q).mp
  cases q with
  | none =>
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    exact CNF.mem_of (h v) (CNF.Clause.mem_of (p:=true) (by simp [guardSafety]))
  | some v =>
    exact CNF.mem_of (h v) (CNF.Clause.mem_of (p:=false) (by simp [guardSafety]))

theorem fresh_guard_width {V : Type*} [DecidableEq V] [Fintype V]
    (F : CNF V) (s : DeclaredOrder V) (h3 : ∀ a∈F,a.length≤3) :
    ∀ a∈guardedInOrder F s.roster,a.length≤4 := by
  intro a ha
  exact J7R9SourceInput.width_four F h3 a
    ((ordered_guard_perm F s.roster s.distinct s.complete).mem_iff.mp ha)

theorem fresh_submitted_CNF_count {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (F : CNF V) (s : DeclaredOrder V) (optOrder : DeclaredOrder (Option V)) :
    let H := guardedInOrder F s.roster
    Nat.card {x : Fin (nWires H)→Bool //
      coreA (freshPlant H optOrder) x=true ∧ coreB (freshPlant H optOrder) x=true} =
        1+PinnedCNF.modelCount F := by
  dsimp only
  rw [fresh_model_count _ _ (fresh_guard_allOccur F s.roster s.complete)]
  exact ordered_guard_count F s.roster s.distinct s.complete

def freshCodec {V : Type} [DecidableEq V] [Fintype V] (H : CNF V) (s : DeclaredOrder V)
    (r c d : ℕ) (rf : Fintype.card (OrderedOld H)≤2^r) (cf : nSubdiv H≤2^c)
    (df : ∀ v : OrderedOld H,orderedDegree H v≤2^d) :
    LiteralCodec (freshPlant H s) r c d where
  rowCode := fun v=>wordAt r ((rosterRank H s) v).val
  distinctRows := by
    intro u v e
    apply (rosterRank H s).injective
    apply Fin.ext
    exact wordAt_rank_inj (((rosterRank H s) u).isLt.trans_le rf)
      (((rosterRank H s) v).isLt.trans_le rf) e
  columnFit := cf
  portFit := df

theorem paid_fresh_root_padded_pass {V : Type} [DecidableEq V] [Fintype V]
    (H : CNF V) (s : DeclaredOrder V) {r c d : ℕ}
    (C : LiteralPortFile (freshPlant H s) r c d) :
    let run := generatedPaddedPorts (nWires H) C.raw
    run.result=(actualWires (nWires H)).map (trueMounted C) ∧ run.result.length=M (nWires H) ∧
      (run.result.map (fun row=>row.base.key)).Nodup ∧
        run.steps≤paddedPortsFee (nWires H) r c d :=
  generated_padded_ports_exact C

theorem fresh_root_uses_actual_stable_seat {V : Type} [DecidableEq V] [Fintype V]
    (H : CNF V) (s : DeclaredOrder V) {r c d : ℕ}
    (C : LiteralPortFile (freshPlant H s) r c d) (p : RootWire (nWires H)) :
    let m := nWires H
    let raw := (trueMounted C p).base.anchor.anchor.physical.seat
    let widths := printed_rank_width m
    let chart := stableRootPacking m (printedHalf m) (nSubdiv H) (printedRankWidth m) (freshPlant H s)
      (constantRootWord m) (printed_room m) (printed_half_correct m)
      widths.2.1 widths.2.2.le
    ∃ h : AOracleMachineTime.bitsValue raw.page<K m,
      decodePhysical (rankAt m p).1 raw h=chart.seat p :=
  serialized_same_stable_seat C p

#print axioms fresh_guard_allOccur
#print axioms fresh_guard_width
#print axioms fresh_submitted_CNF_count
#print axioms freshCodec
#print axioms paid_fresh_root_padded_pass
#print axioms fresh_root_uses_actual_stable_seat
end
end J6R51Ingress
