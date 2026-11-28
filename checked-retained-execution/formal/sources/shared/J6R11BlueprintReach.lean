import J6R11BlueprintAdapter
import J6R10ReachableSchedule

/-! The native finite dependent tree and the actual adapted R9 program
have exactly the same generated records; neither includes arbitrary raw
Call records. -/
namespace J6R11Blueprint
open scoped Polynomial
open J6ActiveRun J6R9Recursive J6R10Reachable

universe uh
variable {Host : Type uh}
variable (N : NativeShape Host) (C : NativeChildren N) (r : Call Host)
variable [DecidableEq (Envelope N C r)]
variable (hW : PositiveData N C r) (f : ℤ[X]) (ell : ℕ)
variable (entries : ∀ c : Call Host, (Fin c.edges → Bool) → List (IntRing f ell))

theorem paddedBlueprint_native_to_reach {c d : Call Host}
    (hc : IsNative N C r c)
    (start : Reach (paddedBlueprint N C r hW f ell entries).program r c)
    (tail : NativeReach (nativePlan N C) c d) :
    Reach (paddedBlueprint N C r hW f ell entries).program r d := by
  induction tail with
  | reflexive => exact start
  | @step c d w next ih =>
    let z := nativeAddressEquiv N C r c hc w.property (hW c hc w.property) w.val
    have hstep : Reach (paddedBlueprint N C r hW f ell entries).program r
        ((paddedBlueprint N C r hW f ell entries).program.child c z) :=
      Reach.down start w.property z
    rw [paddedBlueprint_child N C r hW f ell entries c hc w.property z,
      show z = nativeAddressEquiv N C r c hc w.property (hW c hc w.property) w.val from rfl,
      widenedChild_exact N C r c hc w.property (hW c hc w.property) w.val] at hstep
    exact ih (nativeReach_trans _ hc (NativeReach.step w (NativeReach.reflexive _))) hstep

theorem paddedBlueprint_exact_reachable (c : Call Host) :
    Reach (paddedBlueprint N C r hW f ell entries).program r c ↔ IsNative N C r c := by
  constructor
  · intro h
    exact valid_on_reach _ _ h (NativeReach.reflexive r)
      (paddedBlueprint_closed N C r hW f ell entries)
  · intro h
    exact paddedBlueprint_native_to_reach N C r hW f ell entries (NativeReach.reflexive r) Reach.base h

#print axioms paddedBlueprint_native_to_reach
#print axioms paddedBlueprint_exact_reachable
end J6R11Blueprint