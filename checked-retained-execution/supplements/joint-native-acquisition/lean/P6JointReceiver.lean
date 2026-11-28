import P6Joint
import J8R59SignedReceipt

open scoped Polynomial Classical BigOperators
open Polynomial NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J6R14SpecializedBox J6R9Recursive

namespace P6Joint
noncomputable section
set_option linter.unusedSectionVars false
variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

theorem lower_actual_singleton_eq_joint (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k M q ell : ℕ) (hpq : 10 * M ≤ q) (hℓ : 0 < ell) (f : ℤ[X])
    (addr : Fin f.natDegree → Bool) (actual : Box f ell q)
    (hActual : actual =
      J6ActiveInterpolation.scalarIn q f ell (jointObservation d e even hL a F sign tail b kt k q f addr)) :
    reduceScalar (10 * M) q hpq f (atZero q f ell hℓ actual) =
      jointObservation d e even hL a F sign tail b kt k (10 * M) f addr := by
  rw [hActual, atZero_scalarIn]
  exact jointObservation_reduce d e even hL a F sign tail b kt k _ q hpq f addr

#print axioms lower_actual_singleton_eq_joint
end
end P6Joint
