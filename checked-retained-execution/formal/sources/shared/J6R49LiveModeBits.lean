import J6R48DFSModeLoop
import J6R21LeafWidth

/-! A concrete bit-field bound at the suspension point of a mode event.
The two numeric buffers use their literal UV payloads. Cursor space
uses R15's fixed-width field tariff, not the Lean runtime heap. -/
namespace J6R49LiveBits
open J6R48DFS J6R15ModeCost J6R21Leaf A1R10

set_option autoImplicit false

def accumulatorPayload {p ell : ℕ} {fw : List (A1R10.Word p)}
    (outer inner : UVBlock fw ell) : List Bool :=
  leafPayload outer ++ leafPayload inner

theorem accumulator_payload_width {p ell : ℕ} {fw : List (A1R10.Word p)}
    (outer inner : UVBlock fw ell) :
    (accumulatorPayload outer inner).length = 2 * ell * (fw.length*p) := by
  simp only [accumulatorPayload,List.length_append,leaf_payload_width,two_mul,Nat.add_mul]

def suspendedModeBits {p q ell : ℕ} {fw : List (A1R10.Word p)}
    (s : State q) (out : Pulse q) (outer inner : UVBlock fw ell) : ℕ :=
  modeBoundaryWords s out * (q+1) + (accumulatorPayload outer inner).length

theorem actual_event_buffers_fit {p q n ell : ℕ} {fw : List (A1R10.Word p)}
    (s : State q) (hs : s.wellFormed n) (outer inner : UVBlock fw ell) :
    suspendedModeBits s (untilEvent n (2*n+1) s).result outer inner ≤
      (2*(n+2)^2+n)*(q+1) + 2*ell*(fw.length*p) := by
  rw [suspendedModeBits, accumulator_payload_width]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (event_cursor_live_bound s hs)) _

#print axioms accumulator_payload_width
#print axioms actual_event_buffers_fit
end J6R49LiveBits


