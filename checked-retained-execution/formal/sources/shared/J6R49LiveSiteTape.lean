import J6R49LiveStackMode
import J6R16ModeCostMeter
import J6R24MeteredRecursionFrame

/-! Specialize the suspended-mode bound to the real source variable
tape and the monic arithmetic frame. No complete mode list is needed. -/
namespace J6R49LiveBits
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R32StatefulArithmetic J6R16ModeCost J6R15ModeCost A1R10

set_option autoImplicit false

variable {f : ℤ[X]} {ell s C : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem real_site_tape_width (cfg : RootBounds s C f) (hr : Stable s C r)
    (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (h : NativeReach (Plan sel) r c) (d : Ready S (sourceDelta s) c) (t : Center S c)
    {q : ℕ} (I : SiteTape sel d t q) :
    I.words.length≤rosterSize s C := by
  have he := congrArg List.length I.weightMeaning
  simp only [List.length_map] at he
  rw [he]
  exact roster_size_bound cfg sel h hr hzero hroot d t I.modes I.nodup I.allModes

theorem real_tape_suspension_fit (cfg : RootBounds s C f) (hr : Stable s C r)
    (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (h : NativeReach (Plan sel) r c) (d : Ready S (sourceDelta s) c) (t : Center S c)
    {q : ℕ} (hq : q≤uniformWidth s C) (I : SiteTape sel d t q) (hf : f.Monic)
    (F : J6R24MeteredRecursion.Frame f (registerPrecision S c t))
    (st : J6R15ModeCost.State q) (hst : st.wellFormed I.words.length)
    (outer inner : UVBlock F.words ell) :
    suspendedModeBits st (untilEvent I.words.length (2*I.words.length+1) st).result outer inner ≤
      frameBase (uniformWidth s C) (rosterSize s C) +
        c.edges * frameSlope s C ell f.natDegree := by
  have b := suspended_mode_bits_by_current_edges cfg sel h hr hzero hroot
    d.active t st hst outer inner
  have n := real_site_tape_width cfg hr hzero hroot h d t I
  refine b.trans ?_
  unfold frameBase frameSlope
  rw [F.natDegree hf]
  gcongr

#print axioms real_site_tape_width
#print axioms real_tape_suspension_fit
end J6R49LiveBits

