import J8R59PhysicalReceipts

open scoped Polynomial Classical BigOperators
open Polynomial NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler

namespace P6Joint
noncomputable section
set_option linter.unusedSectionVars false

section Linearity
variable {R Ω S I : Type*} [Fintype R] [DecidableEq R] [Fintype Ω]
  [Fintype S] [DecidableEq S] [Fintype I]

theorem integralChild_linear (weight : Ω → Source) (sign : S → Bool)
    (base : ((S → Bool) × Ω) → R → Bool → Source[X]) (mark : Option (R × Bool))
    (a : I → Source) (feature : I → ((S → Bool) × Ω) → Source) :
    integralChild weight sign base mark (fun x => ∑ i, a i * feature i x) =
    ∑ i, C (a i) * integralChild weight sign base mark (feature i) := by
  let term (x : Ω) (bits : S → Bool) (i : I) :=
    C (a i) * (C (pinWeightSource sign bits * (weight x * feature i (bits,x))) *
      ∏ r : R, J8SourceMoment.rowFactor (J8SourceMoment.marker mark r)
        (base (bits,x) r false) (base (bits,x) r true))
  calc
    _ = ∑ x, ∑ bits, ∑ i, term x bits i := by
      simp only [integralChild, Finset.mul_sum, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro bits _
      apply Finset.sum_congr rfl
      intro i _
      simp only [term, map_mul]
      ring
    _ = ∑ x, ∑ i, ∑ bits, term x bits i := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ bits, term x bits i := Finset.sum_comm
    _ = _ := by simp only [term, integralChild, Finset.mul_sum]

theorem integralChild_add (weight : Ω → Source) (sign : S → Bool)
    (base : ((S → Bool) × Ω) → R → Bool → Source[X]) (mark : Option (R × Bool))
    (f g : ((S → Bool) × Ω) → Source) :
    integralChild weight sign base mark (fun x => f x + g x) =
    integralChild weight sign base mark f + integralChild weight sign base mark g := by
  simp only [integralChild, mul_add, map_add, add_mul, Finset.sum_add_distrib]

end Linearity

variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def jointSource (e : EndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) : Source[X] :=
  let src := liftedGroup d F (physicalBase d e even (J9FactorBounds.kernel L) tail)
    sign (d.pinLabel a) none
  (∑ q : OldTile d a,
    C ((ordinal d (ordinaryWire d q.1) : Source)^(b : ℕ)) *
      src (fun x => sourceBit (x.2 (tileOldInSource d q).1 (tileOldInSource d q).2))) +
  ∑ i : Fin (Fintype.card (PinTile d a)),
    C ((ordinal d (pinWire d (pinEnumeration d a i).1) : Source)^(b : ℕ)) *
      src (fun x => sourceBit (x.1 (tilePinInSource d (pinEnumeration d a i))))

theorem jointSource_eq (e : EndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) :
    jointSource d e even a F sign tail b = groupedSource d e even a F sign tail b := by
  unfold jointSource groupedSource liftedGroup integralFeature
  dsimp only
  simp_rw [mul_comm (sourceBit (_ : Bool)) (_ ^ (_ : ℕ))]
  rw [integralChild_add, integralChild_linear, integralChild_linear]

def jointObservation (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree → Bool) : Scalar q f :=
  groupedProbe q f (k+1+(b:ℕ)) (groupedTargets d a) (groupedPublic d e even a F sign tail)
    (jointSource d e even a F sign tail b) (groupedTarget d e even a F sign tail)
    (physicalKernel d a even hL (J9FactorBounds.kernel L) b kt) (probe q f addr)

theorem jointObservation_eq (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree → Bool) :
    jointObservation d e even hL a F sign tail b kt k q f addr =
    highObservation d e even hL a F sign tail b kt k q f addr := by
  rw [jointObservation, jointSource_eq, highObservation]

theorem jointObservation_reduce (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k p q : ℕ) (hpq : p ≤ q) (f : ℤ[X]) (addr : Fin f.natDegree → Bool) :
    reduceScalar p q hpq f (jointObservation d e even hL a F sign tail b kt k q f addr) =
    jointObservation d e even hL a F sign tail b kt k p f addr := by
  unfold jointObservation
  exact groupedProbe_reduce _ _ hpq _ _ _ _ _ _ _ _

#print axioms integralChild_linear
#print axioms integralChild_add
#print axioms jointSource_eq
#print axioms jointObservation_eq
#print axioms jointObservation_reduce

end
end P6Joint
