import J6R9HermiteRing
import J6ActiveNormalizer
import J6ActiveHermite

/-! Connecting finite Taylor jets to the quotient-jet premises of the
coefficient assembly. Only the retained local degrees are required. -/
namespace J6R9Hermite

open scoped Polynomial BigOperators
open Polynomial DenominatorBudget J6ActiveSchedule

theorem quotient_received_of_low_jet {A B : Type*} [CommRing A] [CommRing B]
    (recv : A→+*B) (k : ℕ) (E F : A[X]) (seen : B[X])
    (input : ∀ j<k, seen.coeff j = recv (F.coeff j)) :
    J6ActiveNormalizer.quotientJet k (E.map recv) seen =
      (J6ActiveNormalizer.quotientJet k E F).map recv := by
  rw [J6ActiveNormalizer.quotientJet_map]
  change J6ActiveHermite.dividedJet k (E.map recv) seen =
    J6ActiveHermite.dividedJet k (E.map recv) (F.map recv)
  exact J6ActiveHermite.dividedJet_congr k (E.map recv) seen (F.map recv)
    (fun j hj => by rw [coeff_map]; exact input j hj)

section ActualJets

variable {A K C : Type*} [CommRing A] [CommRing K] [CommRing C] [Algebra ℚ K]
variable {B : ℤ→Type*} [∀ t, CommRing (B t)]

/-- A true active child may supply a Taylor polynomial only through the
required precision and degree. The finite divided-jet computation is
then certified without assuming a separately correct quotient oracle. -/
theorem finite_raw_jet_receive_reduced
    (ι : A→+*K) (scalars : TwoLocal→+*A)
    (compat : ∀ z, ι (scalars z)=algebraMap ℚ K (twoLocalRat z))
    (a M u p : ℕ) (hM : u≤M)
    (recv : ∀ t, A→+*B t)
    (kernel : ∀ t∈active a M u, RingHom.ker (recv t) =
      Ideal.span ({(2:A)^childPrecision p a M u t}:Set A))
    (E F : ℤ → Polynomial A) (seen : ∀ t : ℤ, Polynomial (B t))
    (received : ∀ t∈active a M u, ∀ j<order M u t,
      (seen t).coeff j=recv t ((F t).coeff j))
    (lift : ℤ→ℕ→A) (out : A)
    (lifted : ∀ t∈active a M u, ∀ j<order M u t,
      recv t (lift t j) =
        (J6ActiveNormalizer.quotientJet (order M u t) ((E t).map (recv t)) (seen t)).coeff j)
    (correct : linearRecompose a M u
      (fun t j => ι ((J6ActiveNormalizer.quotientJet (order M u t) (E t) (F t)).coeff j))
      =ι out)
    (receiver : A→+*C) (nilpotent : (2:C)^p=0) :
    ∃ z : A, ι z=linearRecompose a M u (fun t j => ι (lift t j)) ∧
      receiver z=receiver out := by
  apply finite_ring_receive_reduced ι scalars compat a M u p hM lift _ out correct
     _ receiver nilpotent
  intro t ht j hj
  apply kernel_power_divisibility (recv t) _ (kernel t ht)
  rw [lifted t ht j hj,
    quotient_received_of_low_jet (recv t) (order M u t) (E t) (F t) (seen t) (received t ht),
    coeff_map]

end ActualJets

#print axioms quotient_received_of_low_jet
#print axioms finite_raw_jet_receive_reduced
end J6R9Hermite

