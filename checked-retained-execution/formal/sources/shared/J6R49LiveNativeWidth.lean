import J6R49LiveModeBits
import J6R16ModeCostUniform

/-! Keep the actual edge count when bounding a suspended numeric frame.
The older uniform register envelope replaces it by the root scale. -/
namespace J6R49LiveBits
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R15ModeCost A1R10

set_option autoImplicit false
set_option exponentiation.threshold 12000

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
include cfg

theorem register_bits_by_current_edges
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r)
    (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (active : (S).cutoff<c.edges) (t : Center S c) :
    registerPrecision S c t ≤ siteConstant C*c.edges*s := by
  let lam := Nat.clog 2 s
  let L := stepL lam c.depth
  let u := stepU lam c.depth
  let a := stepA lam c.depth
  obtain ⟨hu,_,_,hP⟩ := register_envelope cfg sel h hr hzero hroot active t
  have hV : registerPrecision S c t≤registerPrecision S c t*u :=
    Nat.le_mul_of_pos_right _ hu
  have hL : L≤s := by
    have h0 : 0<L := by unfold L stepL; positivity
    have bound := (dimensions_small s c.depth cfg.widthPos).1
    exact ((show L≤L^1000 from
      (pow_one L).symm.trans_le (Nat.pow_le_pow_right h0 (by decide))).trans bound.le)
  have hD : 2^(a-padicValInt 2 t.val)≤s :=
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)).trans hL
  exact hV.trans (hP.trans (Nat.mul_le_mul_left _ hD))

theorem suspended_mode_bits_by_current_edges
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r)
    (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (active : (S).cutoff<c.edges) (t : Center S c)
    {q n : ℕ} (st : J6R15ModeCost.State q) (hst : st.wellFormed n)
    {fw : List (A1R10.Word (registerPrecision S c t))} (outer inner : UVBlock fw ell) :
    suspendedModeBits st (untilEvent n (2*n+1) st).result outer inner ≤
      (2*(n+2)^2+n)*(q+1) + c.edges * (2*ell*fw.length*siteConstant C*s) := by
  refine (actual_event_buffers_fit st hst outer inner).trans ?_
  apply Nat.add_le_add_left
  calc
    _ ≤ 2*ell*(fw.length*(siteConstant C*c.edges*s)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (register_bits_by_current_edges cfg sel h hr hzero hroot active t))
    _ = _ := by ring

#print axioms register_bits_by_current_edges
#print axioms suspended_mode_bits_by_current_edges
end J6R49LiveBits


