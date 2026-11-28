import J6R11BlueprintNetwork
import J6R11CollisionReindex

/-! The next layout is constructed from the actual host's finite incidence
and degree, not supplied as an independently authorized state. -/
namespace J6R11Repack
open scoped Classical Polynomial
open P11FullPacking J6R10Repack J6R11Blueprint
variable {f : ℤ[X]} {ell : ℕ} {G : Type} [LinearOrder G] [Fintype G]

def GoodDegree (H : PhysicalHost f ell) (Δ : ℕ) : Prop :=
  (∀ v : H.Row, Nat.card {e : H.Edge // H.network.row e=v} ≤ Δ) ∧
  (∀ v : H.Col, Nat.card {e : H.Edge // H.network.col e=v} ≤ Δ)

def GoodTags (H : PhysicalHost f ell) (p : ℕ) : Prop :=
  ∀ v : H.Row ⊕ H.Col, (H.file v).created ≤ p

theorem host_card (H : PhysicalHost f ell) :
    Nat.card H.Edge = H.edgeCount := by
  letI := H.finiteEdge
  exact Nat.card_eq_fintype_card

theorem host_can_repack (H : PhysicalHost f ell) (a Δ : ℕ) (hG : Fintype.card G=64)
    (degree : GoodDegree H Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ ≤ H.edgeCount)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a ≤ H.edgeCount) :
    ∃ P : PhysicalPacking H.network a G, P.copies =
      ceilCopies (2^a) (maxFiber (declaredCell H.network P.rowLabel P.colLabel)) := by
  letI := H.finiteEdge
  letI := H.finiteRow
  letI := H.finiteCol
  exact J6R11CollisionReindex.child_simple_exists_Pack H.network Δ hG degree.1 degree.2
    (by rwa [host_card]) (by rwa [host_card])

#print axioms host_card
#print axioms host_can_repack
end J6R11Repack
