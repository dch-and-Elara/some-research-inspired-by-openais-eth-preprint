import J6ActiveSchedule
import J6RecursiveMenu

/-! Typed well-founded execution of the Appendix D child schedule. Every
child obtains its exact centre-dependent p_t, depth+1, and source group.
The remaining local proof obligations are the leaf and active assembly
equations. In particular this file does not assume an oracle returning the
final answers to generated children, and does not itself prove the
arithmetic active assembly equation or the geometric packing certificate. -/
namespace J6ActiveRun
open J6ActiveSchedule

structure Call (Host : Type*) where
  host : Host
  depth : ℕ
  edges : ℕ
  prec : ℕ

structure Shape (Host Mode : Type*) where
  cutoff : ℕ
  levelWidth : ℕ → ℕ
  levelBits : ℕ → ℕ
  weight : Call Host → ℤ → Mode → ℕ

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]

abbrev Center (S : Shape Host Mode) (c : Call Host) :=
  {t : ℤ // t ∈ active (S.levelBits c.depth) c.edges (S.levelWidth c.depth)}

def registerPrecision (S : Shape Host Mode) (c : Call Host) (t : Center S c) : ℕ :=
  childPrecision c.prec (S.levelBits c.depth) c.edges (S.levelWidth c.depth) t.val

abbrev Probe (S : Shape Host Mode) (c : Call Host) :=
  Fin (J9PrintedSchedule.probeCount c.edges (2^S.levelBits c.depth))

abbrev Modes (S : Shape Host Mode) (c : Call Host) (t : Center S c) :=
  {b : Mode →₀ ℕ // b ∈ J6RecursiveMenu.menu (registerPrecision S c t) (S.weight c t.val)}

structure Address (S : Shape Host Mode) (c : Call Host) where
  t : Center S c
  zeta : Probe S c
  beta : Modes S c t
  group : Fin 64

theorem address_mode_exact (S : Shape Host Mode) (c : Call Host) (t : Center S c)
    (hw : ∀ m, 0 < S.weight c t.val m) (β : Mode →₀ ℕ) :
    β ∈ J6RecursiveMenu.menu (registerPrecision S c t) (S.weight c t.val)
      ↔ J6RecursiveMenu.weighted (S.weight c t.val) β < registerPrecision S c t :=
  J6RecursiveMenu.exact_printed_menu _ _ hw _

structure Program (S : Shape Host Mode) (Value : ℕ → Type*) where
  childHost : ∀ c, Address S c → Host
  childEdges : ∀ c, Address S c → ℕ
  edgeBound : ∀ c, S.cutoff < c.edges → ∀ w,
    32 * childEdges c w ≤ 3 * c.edges
  leaf : ∀ c : Call Host, Value c.prec
  assemble : ∀ c : Call Host, (∀ w : Address S c, Value (registerPrecision S c w.t)) → Value c.prec

variable {S : Shape Host Mode} {Value : ℕ → Type*}

def Program.child (P : Program S Value) (c : Call Host) (w : Address S c) : Call Host :=
  ⟨P.childHost c w, c.depth+1, P.childEdges c w, registerPrecision S c w.t⟩

theorem Program.child_smaller (P : Program S Value) (c : Call Host) (h : S.cutoff < c.edges)
    (w : Address S c) : (P.child c w).edges < c.edges :=
  (child_shrinks _ _ (Nat.zero_lt_of_lt h) (P.edgeBound c h w)).2

theorem Program.child_higher_precision (P : Program S Value) (c : Call Host)
    (h : S.cutoff < c.edges) (w : Address S c) :
    c.prec < (P.child c w).prec :=
  child_monotone _ _ _ _ _ (Nat.zero_lt_of_lt h)

def Program.run (P : Program S Value) (c : Call Host) : Value c.prec :=
  if _h : c.edges ≤ S.cutoff then
    P.leaf c
  else
    P.assemble c (fun w => P.run (P.child c w))
termination_by c.edges
decreasing_by exact P.child_smaller c (Nat.lt_of_not_ge _h) w

theorem Program.run_verified (P : Program S Value) (expect : ∀ c : Call Host, Value c.prec)
    (hleaf : ∀ c, c.edges ≤ S.cutoff → P.leaf c = expect c)
    (hactive : ∀ c, S.cutoff < c.edges →
      P.assemble c (fun w => expect (P.child c w)) = expect c)
    (c : Call Host) : P.run c = expect c := by
  rw [Program.run]
  split
  · rename_i h
    exact hleaf c h
  · rename_i h
    have hh : S.cutoff < c.edges := Nat.lt_of_not_ge h
    have hfun : (fun w : Address S c => P.run (P.child c w)) =
        (fun w : Address S c => expect (P.child c w)) := by
      funext w
      exact P.run_verified expect hleaf hactive (P.child c w)
    rw [hfun]
    exact hactive c hh
termination_by c.edges
decreasing_by exact P.child_smaller c hh w

#print axioms address_mode_exact
#print axioms Program.child_smaller
#print axioms Program.child_higher_precision
#print axioms Program.run
#print axioms Program.run_verified
end J6ActiveRun