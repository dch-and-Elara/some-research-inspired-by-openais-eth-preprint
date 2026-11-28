import P6JointDP
import P6JointReceiverPartitions

open scoped Polynomial BigOperators Classical
open Polynomial NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
namespace P6Joint
open BoundaryPlan
noncomputable section
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def oldFeature (a : S) (y : OldTile d a)
    (x : (LocalPin d (d.pinLabel a) → Bool) × LocalBits d (d.pinLabel a)) : Source :=
  sourceBit (x.2 (tileOldInSource d y).1 (tileOldInSource d y).2)

def pinFeature (a : S) (i : Fin (Fintype.card (PinTile d a)))
    (x : (LocalPin d (d.pinLabel a) → Bool) × LocalBits d (d.pinLabel a)) : Source :=
  sourceBit (x.1 (tilePinInSource d (pinEnumeration d a i)))

/-- The ring, point and base are parameters. The plans for each group,
column bit and row leg are consequently independent of moment order b. -/
structure PhysicalSlotPool {K : Type*} [CommRing K]
    (a : S) (F : OldTables d) (base : IntegralArguments d) (sign : S → Bool)
    (φ : Source[X] →+* K) (w : ℕ) where
  sibling : (g : G) → PhysicalGroupPlan d F base sign g φ w none (fun _ => 1)
  old : (y : OldTile d a) → PhysicalGroupPlan d F base sign (d.pinLabel a) φ w none (oldFeature d a y)
  pin : (i : Fin (Fintype.card (PinTile d a))) →
    PhysicalGroupPlan d F base sign (d.pinLabel a) φ w none (pinFeature d a i)
  target : (x : TargetPorts d a) →
    PhysicalGroupPlan d F base sign (d.rowLabel (pinWire d a).1) φ w (some x) (fun _ => 1)

def slotFromPool (e : EndpointSeating d) (even : Even L) (hL : 2<L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree → Bool)
    (w : ℕ) (pool : PhysicalSlotPool d a F (physicalBase d e even (J9FactorBounds.kernel L) tail) sign
      (Polynomial.eval₂RingHom (toScalar q f) (2*probe q f addr)) w) : Scalar q f :=
  let z := probe q f addr
  let φ := Polynomial.eval₂RingHom (toScalar q f) (2*z)
  let kB := (2 : Scalar q f)^(k+1+(b:ℕ)) * z
  let pub := ∏ g ∈ ((Finset.univ : Finset G).erase (d.pinLabel a)).erase (d.rowLabel (pinWire d a).1),
    denotation (pool.sibling g).plan Fin.elim0
  let src :=
    (∑ y : OldTile d a, φ (C ((ordinal d (ordinaryWire d y.1) : Source)^(b:ℕ))) *
      denotation (pool.old y).plan Fin.elim0) +
    (∑ i : Fin (Fintype.card (PinTile d a)),
      φ (C ((ordinal d (pinWire d (pinEnumeration d a i).1) : Source)^(b:ℕ))) *
        denotation (pool.pin i).plan Fin.elim0)
  let trg := ∑ j ∈ groupedTargets d a, (kB * φ (physicalKernel d a even hL (J9FactorBounds.kernel L) b kt j)) *
    denotation (pool.target j).plan Fin.elim0
  (pub * src) * trg

theorem slotFromPool_exact (e : EndpointSeating d) (even : Even L) (hL : 2<L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree → Bool)
    (w : ℕ) (pool : PhysicalSlotPool d a F (physicalBase d e even (J9FactorBounds.kernel L) tail) sign
      (Polynomial.eval₂RingHom (toScalar q f) (2*probe q f addr)) w) :
    slotFromPool d e even hL a F sign tail b kt k q f addr w pool =
    slotFromPartitions d e even hL a F sign tail b kt k q f addr := by
  unfold slotFromPool slotFromPartitions
  dsimp only
  have hs (g : G) := (PhysicalGroupPlan.correct _ _ _ _ _ _ _ _ _ (pool.sibling g)).1
  have ho (y : OldTile d a) := (PhysicalGroupPlan.correct _ _ _ _ _ _ _ _ _ (pool.old y)).1
  have hp (i : Fin (Fintype.card (PinTile d a))) :=
    (PhysicalGroupPlan.correct _ _ _ _ _ _ _ _ _ (pool.pin i)).1
  have ht (x : TargetPorts d a) := (PhysicalGroupPlan.correct _ _ _ _ _ _ _ _ _ (pool.target x)).1
  simp only [hs, ho, hp, ht]
  rfl

theorem physicalPool_same_native_receipt (e : EndpointSeating d) (even : Even L) (hL : 2<L)
    (a : S) (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k q ell : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree → Bool)
    (w : ℕ) (pool : PhysicalSlotPool d a F (physicalBase d e even (J9FactorBounds.kernel L) tail) sign
      (Polynomial.eval₂RingHom (toScalar q f) (2*probe q f addr)) w)
    (actual : J6R9Recursive.Box f ell q)
    (hActual : actual = J6ActiveInterpolation.scalarIn q f ell
      (slotFromPartitions d e even hL a F sign tail b kt k q f addr)) :
    actual = J6ActiveInterpolation.scalarIn q f ell
      (slotFromPool d e even hL a F sign tail b kt k q f addr w pool) :=
  hActual.trans (congrArg (J6ActiveInterpolation.scalarIn q f ell)
    (slotFromPool_exact d e even hL a F sign tail b kt k q f addr w pool).symm)

#print axioms physicalPool_same_native_receipt

theorem physicalPool_same_10M_receipt (e : EndpointSeating d) (even : Even L) (hL : 2<L)
    (a : S) (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k M q ell : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree → Bool)
    (w : ℕ) (pool : PhysicalSlotPool d a F (physicalBase d e even (J9FactorBounds.kernel L) tail) sign
      (Polynomial.eval₂RingHom (toScalar (10*M) f) (2*probe (10*M) f addr)) w)
    (hpq : 10*M≤q) (hℓ : 0<ell)
    (actual : J6R9Recursive.Box f ell q)
    (hActual : actual = J6ActiveInterpolation.scalarIn q f ell
      (slotFromPartitions d e even hL a F sign tail b kt k q f addr)) :
    reduceScalar (10*M) q hpq f (J6R14SpecializedBox.atZero q f ell hℓ actual) =
        slotFromPool d e even hL a F sign tail b kt k (10*M) f addr w pool :=
  (lower_actual_singleton_eq_partitions d e even hL a F sign tail b kt k M q ell hpq hℓ f addr actual hActual).trans
    (slotFromPool_exact d e even hL a F sign tail b kt k (10*M) f addr w pool).symm

#print axioms physicalPool_same_10M_receipt

#print axioms slotFromPool_exact
end
end P6Joint
