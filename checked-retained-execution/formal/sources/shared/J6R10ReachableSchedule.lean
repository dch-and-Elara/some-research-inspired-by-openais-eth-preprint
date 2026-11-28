import J6ActiveRun
import Mathlib.Tactic

/-! Actual generated calls, and only those calls. Labels record a legal
printed centre, binary residue probe, weighted mode and physical group;
the parent must be strictly above the leaf cutoff. The estimates use
the printed 32m≤3M edge bound, not arbitrary raw records. -/
namespace J6R10Reachable
open J6ActiveRun J6ActiveSchedule

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {S : Shape Host Mode} {Value : ℕ → Type*}

inductive Reach (P : Program S Value) (root : Call Host) : Call Host → Prop
  | base : Reach P root root
  | down {c : Call Host} (prior : Reach P root c) (active : S.cutoff < c.edges)
      (w : Address S c) : Reach P root (P.child c w)

theorem child_edges_eighth (P : Program S Value) (c : Call Host)
    (hc : S.cutoff < c.edges) (w : Address S c) : 8*(P.child c w).edges ≤ c.edges :=
  (child_shrinks _ _ (Nat.zero_lt_of_lt hc) (P.edgeBound c hc w)).1

theorem child_precision_increment (P : Program S Value) (c : Call Host) (w : Address S c) :
    (P.child c w).prec = c.prec +
      8*height c.edges (S.levelWidth c.depth)*(2^S.levelBits c.depth / 2^(padicValInt 2 w.t.val)) +
      8*c.edges*(S.levelBits c.depth + 1) := by
  change J9PrintedSchedule.precision c.prec
    (height c.edges (S.levelWidth c.depth))
    (2^S.levelBits c.depth / 2^(padicValInt 2 w.t.val)) c.edges (S.levelBits c.depth) = _
  unfold J9PrintedSchedule.precision
  omega

theorem reach_depth (P : Program S Value) {root c : Call Host}
    (h : Reach P root c) : root.depth ≤ c.depth := by
  induction h with
  | base => exact le_rfl
  | down h _ w ih =>
    exact ih.trans (Nat.le_succ _)

theorem reach_edge_power (P : Program S Value) {root c : Call Host}
    (h : Reach P root c) : 8^(c.depth-root.depth)*c.edges ≤ root.edges := by
  induction h with
  | base => simp
  | @down c h hc w ih =>
    have hd := reach_depth P h
    have he : (P.child c w).depth-root.depth = (c.depth-root.depth)+1 := by
      change c.depth+1-root.depth = _
      omega
    rw [he,pow_succ,mul_assoc]
    exact (Nat.mul_le_mul_left _ (child_edges_eighth P c hc w)).trans ih

theorem reach_depth_add_edges (P : Program S Value) {root c : Call Host}
    (h : Reach P root c) : (c.depth-root.depth)+c.edges ≤ root.edges := by
  induction h with
  | base => simp
  | @down c h hc w ih =>
    have hd := reach_depth P h
    have he : (P.child c w).depth-root.depth = (c.depth-root.depth)+1 := by
      change c.depth+1-root.depth = _
      omega
    have hs := P.child_smaller c hc w
    rw [he]
    omega

theorem reach_bounded_depth (P : Program S Value) {root c : Call Host}
    (h : Reach P root c) : c.depth ≤ root.depth+root.edges := by
  have h₁ := reach_depth P h
  have h₂ := reach_depth_add_edges P h
  omega

theorem reach_precision (P : Program S Value) {root c : Call Host}
    (h : Reach P root c) : root.prec ≤ c.prec := by
  induction h with
  | base => exact le_rfl
  | @down c h hc w ih => exact ih.trans (P.child_higher_precision c hc w).le

theorem reach_precision_strict (P : Program S Value) {root c : Call Host}
    (h : Reach P root c) (hd : root.depth < c.depth) : root.prec < c.prec := by
  cases h with
  | base => exact False.elim ((lt_irrefl _) hd)
  | @down c h hc w => exact (reach_precision P h).trans_lt (P.child_higher_precision c hc w)

theorem valid_on_reach (P : Program S Value) (Valid : Call Host → Prop) {root c : Call Host}
    (h : Reach P root c) (hroot : Valid root)
    (hchild : ∀ c, Valid c → S.cutoff < c.edges → ∀ w, Valid (P.child c w)) :
    Valid c := by
  induction h with
  | base => exact hroot
  | @down c _ hc w ih => exact hchild c ih hc w

theorem source_root_edge_bound (P : Program S Value) {root c : Call Host}
    (h : Reach P root c) (rootDepth : root.depth = 0) (C s : ℕ) (seed : root.edges ≤ C*s) :
    8^c.depth*c.edges ≤ C*s := by
  have he := (reach_edge_power P h).trans seed
  simpa only [rootDepth,Nat.sub_zero] using he

#print axioms source_root_edge_bound
#print axioms child_edges_eighth
#print axioms child_precision_increment
#print axioms reach_edge_power
#print axioms reach_depth_add_edges
#print axioms reach_bounded_depth
#print axioms reach_precision
#print axioms reach_precision_strict
#print axioms valid_on_reach
end J6R10Reachable