import P6JointFactors

open scoped BigOperators Classical Polynomial
open Polynomial NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler

namespace P6Joint
noncomputable section
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]
variable {K : Type*} [CommRing K]

def groupPartition (F : OldTables d) (base : IntegralArguments d)
    (sign : S → Bool) (g : G) (φ : Source[X] →+* K)
    (mark : Option (LocalRow d g × Bool)) (feature : ((LocalPin d g → Bool) × LocalBits d g) → Source) : K :=
  partition (fun x => φ (C (physicalTableWeight d F g x)))
    (fun x r b => φ (base g ((fun i => sign i.1),x) r b))
    mark (fun x => φ (C (feature ((fun i => sign i.1),x))))

theorem liftedGroup_eval_partition (F : OldTables d) (base : IntegralArguments d)
    (sign : S → Bool) (g : G) (φ : Source[X] →+* K)
    (mark : Option (LocalRow d g × Bool)) (feature : ((LocalPin d g → Bool) × LocalBits d g) → Source) :
    φ (liftedGroup d F base sign g mark feature) =
      groupPartition d F base sign g φ mark feature :=
  integralChild_eval_partition _ _ _ _ _ _

def slotFromPartitions (e : EndpointSeating d) (even : Even L) (hL : 2<L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree → Bool) : Scalar q f :=
  let z := probe q f addr
  let φ := Polynomial.eval₂RingHom (toScalar q f) (2*z)
  let base := physicalBase d e even (J9FactorBounds.kernel L) tail
  let gS := d.pinLabel a
  let gT := d.rowLabel (pinWire d a).1
  let kB := (2 : Scalar q f)^(k+1+(b:ℕ)) * z
  let pub := ∏ g ∈ ((Finset.univ : Finset G).erase gS).erase gT,
    groupPartition d F base sign g φ none (fun _ => 1)
  let src :=
    (∑ y : OldTile d a, φ (C ((ordinal d (ordinaryWire d y.1) : Source)^(b:ℕ))) *
      groupPartition d F base sign gS φ none
        (fun x => sourceBit (x.2 (tileOldInSource d y).1 (tileOldInSource d y).2))) +
    (∑ i : Fin (Fintype.card (PinTile d a)),
      φ (C ((ordinal d (pinWire d (pinEnumeration d a i).1) : Source)^(b:ℕ))) *
        groupPartition d F base sign gS φ none
          (fun x => sourceBit (x.1 (tilePinInSource d (pinEnumeration d a i)))))
  let trg := ∑ j ∈ groupedTargets d a, (kB * φ (physicalKernel d a even hL (J9FactorBounds.kernel L) b kt j)) *
    groupPartition d F base sign gT φ (some j) (fun _ => 1)
  (pub * src) * trg

theorem jointObservation_as_partitions (e : EndpointSeating d) (even : Even L) (hL : 2<L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree → Bool) :
    jointObservation d e even hL a F sign tail b kt k q f addr =
      slotFromPartitions d e even hL a F sign tail b kt k q f addr := by
  unfold jointObservation groupedProbe groupedPublic groupedTarget jointSource slotFromPartitions liftedPublic
  dsimp only
  let φ := Polynomial.eval₂RingHom (toScalar q f) (2 * probe q f addr)
  change (φ _ * φ _) * (∑ j ∈ groupedTargets d a, _ * φ _) = _
  simp only [map_mul, map_prod, map_add, map_sum, liftedGroup_eval_partition]
  rfl

#print axioms liftedGroup_eval_partition
#print axioms jointObservation_as_partitions
end 
end P6Joint
