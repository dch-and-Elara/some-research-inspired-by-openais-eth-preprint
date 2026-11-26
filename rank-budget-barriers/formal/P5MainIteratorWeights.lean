import P5MainIteratorOrbit
import Mathlib.Data.Finset.Powerset

/-! Exact binomial mass of the retained source eigenvectors at a physical
orbit. Weighted by the true orbit size, not the global 2^Q. -/
namespace P5MainIterator
open scoped BigOperators Classical

variable {D : Type*} [Fintype D]

noncomputable def trueCoordinates (w : D → Bool) : Finset D :=
  Finset.univ.filter (fun i => w i)

noncomputable def boolFiniteSets : (D→Bool) ≃ Finset D where
  toFun := trueCoordinates
  invFun s i := decide (i∈s)
  left_inv w := by
    funext i
    cases hv : w i <;> simp [trueCoordinates,hv]
  right_inv s := by
    ext i
    simp [trueCoordinates]

/-- Exactly the count of weight-j sign-mode selections, restricted to
the chosen exceptional weights. -/
theorem mask_count (keep : ℕ → Prop) :
    Fintype.card {w : D→Bool // keep (boolWeight w)} =
      ∑ j ∈ (Finset.range (Fintype.card D+1)).filter keep, (Fintype.card D).choose j := by
  let S : Finset (Finset D) := Finset.univ.filter (fun s => keep s.card)
  let P := (Finset.range (Fintype.card D+1)).filter keep
  have aux (w : D→Bool) : keep (boolWeight w) ↔ boolFiniteSets w ∈ S := by
    simp [S,boolFiniteSets,boolWeight,trueCoordinates]
  let e := Equiv.subtypeEquiv (boolFiniteSets (D:=D)) aux
  have hS : S = P.biUnion (fun j => Finset.univ.powersetCard j) := by
    ext s
    constructor
    · intro hs
      have hkeep := (Finset.mem_filter.mp hs).2
      refine Finset.mem_biUnion.mpr ⟨s.card,?_,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _)),hkeep⟩
    · intro hs
      obtain ⟨j,hj,hs⟩ := Finset.mem_biUnion.mp hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_powersetCard.mp hs).2 ▸ (Finset.mem_filter.mp hj).2⟩
  rw [Fintype.card_congr e,Fintype.card_coe,hS,Finset.card_biUnion]
  · simp [P,Finset.card_powersetCard]
  · intro j _ k _ hne
    change Disjoint ((Finset.univ : Finset D).powersetCard j) (Finset.univ.powersetCard k)
    rw [Finset.disjoint_left]
    intro s hs ht
    exact hne ((Finset.mem_powersetCard.mp hs).2.symm.trans (Finset.mem_powersetCard.mp ht).2)

/-- Exact finite fair Binomial probability on a set of permitted weights. -/
noncomputable def binomialMass (n : ℕ) (keep : ℕ → Prop) : ℝ :=
  ↑(∑ j∈(Finset.range (n+1)).filter keep, n.choose j) / (2:ℝ)^n

variable {O : Type*} (A : O → Type*) [Fintype O] [∀ o, Fintype (A o)]

set_option maxHeartbeats 5400000 in
theorem exceptional_slot_energy (keep : ℕ → Prop) (x : OrbitSlots A) :
    (∑ r : Exceptional A keep, (orbitRow A r.val x)^2) =
      binomialMass (Fintype.card (A x.1)) keep := by
  rcases x with ⟨o,x⟩
  let c := ((2:ℝ)^Fintype.card (A o))⁻¹
  let f (r : OrbitSlots A) := (orbitRow A r ⟨o,x⟩)^2
  have hsum :
      (∑ r : Exceptional A keep, f r.val) =
        ∑ r : OrbitSlots A, if keep (boolWeight r.2) then f r else 0 := by
    rw [←Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  change (∑ r : Exceptional A keep, f r.val) = _
  rw [hsum,Fintype.sum_sigma]
  rw [Finset.sum_eq_single o]
  · have hmain :
        (∑ w : A o→Bool, if keep (boolWeight w) then f ⟨o,w⟩ else 0) =
        ∑ w : A o→Bool, if keep (boolWeight w) then c else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      change (if keep (boolWeight w) then (orbitRow A ⟨o,w⟩ ⟨o,x⟩)^2 else 0) = _
      rw [orbitRow_square]
      simp [c]
    rw [hmain,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    have hc :
        (Finset.univ.filter (fun w : A o→Bool => keep (boolWeight w))).card =
          ∑ j ∈ (Finset.range (Fintype.card (A o)+1)).filter keep, (Fintype.card (A o)).choose j := by
      rw [←Fintype.card_coe (Finset.univ.filter (fun w : A o→Bool => keep (boolWeight w)))]
      exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => by simp))).trans (mask_count keep)
    rw [hc]
    rfl
  · intro p _ hp
    apply Finset.sum_eq_zero
    intro a _
    change (if keep (boolWeight a) then (orbitRow A ⟨p,a⟩ ⟨o,x⟩)^2 else 0)=0
    rw [orbitRow_off _ _ _ hp]
    simp
  · simp

#print axioms mask_count
#print axioms exceptional_slot_energy
end P5MainIterator
