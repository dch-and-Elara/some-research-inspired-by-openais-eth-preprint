import PinnedCNF
import IntegralOutputTransfer

/-! Independent composition check. A genuine pinned-CNF matching supplies the
residue determinant. The only terminal hypotheses are an integral lift of the
field-valued sum and correctness of its residue on the matching submatrix. -/

open scoped BigOperators

theorem fullRankForActualPinnedLift {V I J R S K : Type*}
    [Fintype V] [Fintype I] [DecidableEq I] [Fintype J]
    [CommRing R] [CommRing S] [Nontrivial S] [Field K]
    {E : Finset (V × V)} (M : PinnedCNF.InducedMatching E I)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (L : Matrix (I → Bool) (I → Bool) R)
    (terms : J → Matrix (I → Bool) (I → Bool) K)
    (hrep : ∑ j, terms j = embed.mapMatrix L)
    (hres : residue.mapMatrix L = M.countMatrix S) :
    (∑ j, terms j).rank = 2 ^ Fintype.card I := by
  rw [IntegralOutputTransfer.sum_full_rank_of_residue embed residue hinjective L
    (M.countMatrix S) terms hrep hres (M.countMatrix_det_isUnit S).ne_zero,
    Fintype.card_fun, Fintype.card_bool]

#print axioms fullRankForActualPinnedLift
