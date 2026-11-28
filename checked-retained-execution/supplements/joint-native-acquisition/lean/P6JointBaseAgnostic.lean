import P6JointFactors

open scoped Polynomial Classical BigOperators
open Polynomial NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler

namespace P6Joint
noncomputable section
set_option linter.unusedSectionVars false
variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def jointSourceAtBase (a : S)
    (F : OldTables d) (sign : S → Bool) (base : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) : Source[X] :=
  let src := liftedGroup d F base sign (d.pinLabel a) none
  (∑ q : OldTile d a,
    C ((ordinal d (ordinaryWire d q.1) : Source)^(b : ℕ)) *
      src (fun x => sourceBit (x.2 (tileOldInSource d q).1 (tileOldInSource d q).2))) +
  ∑ i : Fin (Fintype.card (PinTile d a)),
    C ((ordinal d (pinWire d (pinEnumeration d a i).1) : Source)^(b : ℕ)) *
      src (fun x => sourceBit (x.1 (tilePinInSource d (pinEnumeration d a i))))

theorem jointSourceAtBase_eq (a : S) (F : OldTables d) (sign : S → Bool)
    (base : IntegralArguments d) (b : Fin (Fintype.card (PinTile d a))) :
    jointSourceAtBase d a F sign base b = liftedGroup d F base sign
      (d.pinLabel a) none (integralFeature d a b) := by
  unfold jointSourceAtBase liftedGroup integralFeature
  dsimp only
  simp_rw [mul_comm (sourceBit (_ : Bool)) (_ ^ (_ : ℕ))]
  rw [integralChild_add, integralChild_linear, integralChild_linear]

#print axioms jointSourceAtBase_eq
end
end P6Joint
