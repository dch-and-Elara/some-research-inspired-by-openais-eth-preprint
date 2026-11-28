import J6R49LiveBits
import J6R49LiveNativeWidth

/-! The counted suspended-mode bits share the genuine occurrence stack.
Only a frame currently waiting at a mode event contributes that event's
two numeric registers and cursor. This is not a liveness theorem for
arbitrary additional machine objects. -/
namespace J6R49LiveBits
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R32StatefulArithmetic J6R48DFS J6R16ModeCost J6R15ModeCost A1R10

set_option autoImplicit false

variable {f : ℤ[X]} {ell s C : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

structure Suspension (x : Call (PhysicalHost f ell)) where
  active : (S).cutoff<x.edges
  center : Center S x
  q : ℕ
  n : ℕ
  state : J6R15ModeCost.State q
  wf : state.wellFormed n
  coeffs : List (A1R10.Word (registerPrecision S x center))
  outer : UVBlock coeffs ell
  inner : UVBlock coeffs ell

def Suspension.bits {x : Call (PhysicalHost f ell)} (a : Suspension (s:=s) x) : ℕ :=
  suspendedModeBits a.state (untilEvent a.n (2*a.n+1) a.state).result a.outer a.inner

def currentModeBits {x : Call (PhysicalHost f ell)} (a : Option (Suspension (s:=s) x)) : ℕ :=
  match a with
  | none => 0
  | some m => m.bits

noncomputable def liveModeBits
    (atPath : {x : Call (PhysicalHost f ell)} → Path sel r x → Option (Suspension (s:=s) x)) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ
  | _, .root => currentModeBits (atPath .root)
  | _, .step p w => liveModeBits atPath p + currentModeBits (atPath (.step p w))

def frameBase (W N : ℕ) : ℕ := (2*(N+2)^2+N)*(W+1)
def frameSlope (s C ell E : ℕ) : ℕ := 2*ell*E*siteConstant C*s

theorem current_mode_bits_fit (cfg : RootBounds s C f) (hr : Stable s C r)
    (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (p : Path sel r c) (W N E : ℕ) (now : Option (Suspension (s:=s) c))
    (fit : ∀ m, now=some m → m.q≤W ∧ m.n≤N ∧ m.coeffs.length≤E) :
    currentModeBits now ≤ frameBase W N + c.edges * frameSlope s C ell E := by
  cases now with
  | none => exact Nat.zero_le _
  | some m =>
    obtain ⟨hq,hn,hE⟩ := fit m rfl
    have b := suspended_mode_bits_by_current_edges cfg sel p.reached hr hzero hroot
      m.active m.center m.state m.wf m.outer m.inner
    change m.bits ≤ _
    refine b.trans ?_
    unfold frameBase frameSlope
    gcongr

theorem live_suspended_modes_geometric (cfg : RootBounds s C f) (hr : Stable s C r)
    (hzero : r.depth=0) (hroot : r.prec≤C*s) (W N E : ℕ)
    (atPath : {x : Call (PhysicalHost f ell)} → Path sel r x → Option (Suspension (s:=s) x))
    (fit : ∀ {x} (p : Path sel r x) m, atPath p=some m → m.q≤W ∧ m.n≤N ∧ m.coeffs.length≤E)
    (p : Path sel r c) :
    liveModeBits atPath p ≤ (pathLimit s C + 1) * frameBase W N +
        (32*r.edges/29) * frameSlope s C ell E := by
  have hsum : liveModeBits atPath p ≤
      (edgeStack p).length * frameBase W N + (edgeStack p).sum * frameSlope s C ell E := by
    induction p with
    | root =>
      simpa only [liveModeBits,edgeStack,List.length_cons,List.length_nil,Nat.zero_add,
        Nat.one_mul,List.sum_cons,List.sum_nil,Nat.add_zero]
        using current_mode_bits_fit cfg hr hzero hroot (Path.root : Path sel r r) W N E
          (atPath .root) (fit .root)
    | @step par p w ih =>
      have hp := current_mode_bits_fit cfg hr hzero hroot (Path.step p w) W N E
        (atPath (.step p w)) (fit (.step p w))
      simp only [liveModeBits,edgeStack,List.length_append,List.length_cons,List.length_nil,
        Nat.zero_add,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_mul]
      exact (Nat.add_le_add ih hp).trans_eq (by ac_rfl)
  have hb : (edgeStack p).sum ≤ (32*r.edges)/29 := by
    have h := edgeStack_geometric p
    omega
  exact hsum.trans (Nat.add_le_add
    (Nat.mul_le_mul_right _ (printed_stack_level_bound cfg hr hzero p))
    (Nat.mul_le_mul_right _ hb))

#print axioms current_mode_bits_fit
#print axioms live_suspended_modes_geometric
end J6R49LiveBits


