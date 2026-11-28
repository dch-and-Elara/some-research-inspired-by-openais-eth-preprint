import J6ActiveSchedule

/-! Exact finite budgets for the signed J9 prefix in the literal
Appendix D schedule. No asymptotic notation enters these bounds. -/
namespace J6R14SpecializedBox
open J6ActiveSchedule

theorem native_register_precision_ge_tenM (p a M u : ℕ) (t : ℤ) (ha : 0<a) :
    10*M ≤ childPrecision p a M u t := by
  have ha' : 10 ≤ 8*(a+1) := by omega
  calc
    10*M = M*10 := Nat.mul_comm _ _
    _ ≤ M*(8*(a+1)) := Nat.mul_le_mul_left M ha'
    _ = 8*M*(a+1) := by ring
    _ ≤ childPrecision p a M u t := by unfold childPrecision J9PrintedSchedule.precision; omega

theorem native_probe_menu_contains_signed_prefix (M L : ℕ) (hL : 6≤L) :
    10*M+1 ≤ J9PrintedSchedule.probeCount M L := by
  have hs : 10 ≤ 2*L-1 := by omega
  have h := Nat.mul_le_mul_left M hs
  unfold J9PrintedSchedule.probeCount J9PrintedSchedule.degreeBound
  rw [Nat.mul_comm 10 M]
  exact Nat.succ_le_succ h

theorem signed_slot_order_legal (n L M p : ℕ) (hN : n<L)
    (hB : L≤M) (hp : 10*M≤p) : n < p-1 := by omega

#print axioms native_register_precision_ge_tenM
#print axioms native_probe_menu_contains_signed_prefix
#print axioms signed_slot_order_legal
end J6R14SpecializedBox