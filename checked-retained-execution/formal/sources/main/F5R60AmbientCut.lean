import F5R60AmbientCore
import Mathlib.Data.Finset.SymmDiff

/-! Exact crossing-edge decomposition and the printed expansion argument
for the two actual halves and their new matching. No expansion condition
on the old half or on the completed graph is taken as an input. -/
namespace F5R60.Ambient
set_option autoImplicit false
open scoped Classical symmDiff

variable {n : ℕ}

abbrev Crossing {A E : Type*} (ends : E → Bool → A) (cut : A → Bool) :=
  {e : E // cut (ends e false) ≠ cut (ends e true)}

abbrev BackCross (B : SimpleGraph (Fin n)) (cut : Fin n → Bool) :=
  {e : ForwardEdge B // cut e.val.1 ≠ cut e.val.2}

abbrev MatchCross (cut : Vertices n → Bool) :=
  {i : Fin n // cut (.inl i) ≠ cut (.inr i)}

def side {A : Type*} [Fintype A] (cut : A → Bool) : Finset A :=
  Finset.univ.filter fun x => cut x = true

theorem card_filter_subtype {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    Nat.card {x // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_of_subtype _ (fun _ => by simp)

noncomputable def cutSize (f : Vertices n → Bool) : ℕ := Nat.card {v // f v = true}

abbrev leftSide (f : Vertices n → Bool) := side (f ∘ Sum.inl)
abbrev rightSide (f : Vertices n → Bool) := side (f ∘ Sum.inr)
abbrev mismatch (f : Vertices n → Bool) := (leftSide f ∆ rightSide f).card
abbrev overlap (f : Vertices n → Bool) := (leftSide f ∩ rightSide f).card

def crossing_equiv (H B : SimpleGraph (Fin n)) (f : Vertices n → Bool) :
    Crossing (ends H B) f ≃
      (BackCross H (f ∘ Sum.inl) ⊕ BackCross B (f ∘ Sum.inr)) ⊕ MatchCross f :=
  Equiv.subtypeSum.trans (Equiv.sumCongr Equiv.subtypeSum (Equiv.refl _))

theorem crossing_count (H B : SimpleGraph (Fin n)) (f : Vertices n → Bool) :
    Nat.card (Crossing (ends H B) f) =
      Nat.card (BackCross H (f ∘ Sum.inl)) + Nat.card (BackCross B (f ∘ Sum.inr)) +
      Nat.card (MatchCross f) := by
  simpa only [Nat.card_sum] using Nat.card_congr (crossing_equiv H B f)

theorem cut_halves_exact (f : Vertices n → Bool) :
    cutSize f = (leftSide f).card + (rightSide f).card := by
  have e : {v : Vertices n // f v = true} ≃
      {j : Fin n // (f ∘ Sum.inl) j = true} ⊕ {j : Fin n // (f ∘ Sum.inr) j = true} :=
    Equiv.subtypeSum
  simpa only [cutSize,Nat.card_sum,card_filter_subtype,side] using Nat.card_congr e

theorem matching_crosses_exactly_symmDiff (f : Vertices n → Bool) :
    Nat.card (MatchCross f) = mismatch f := by
  rw [card_filter_subtype]
  apply congrArg Finset.card
  ext j
  rw [Finset.mem_symmDiff]
  simp only [leftSide,rightSide,side,Finset.mem_filter,Finset.mem_univ,true_and,Function.comp_apply]
  cases f (.inl j) <;> cases f (.inr j) <;> decide

theorem cut_partition (f : Vertices n → Bool) :
    cutSize f = mismatch f + 2*overlap f := by
  let A := leftSide f
  let D := rightSide f
  have hUnion : A ∆ D = (A\D) ∪ (D\A) := rfl
  have hd : Disjoint (A\D) (D\A) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact (Finset.mem_sdiff.mp hk).2 (Finset.mem_sdiff.mp hj).1
  have hl : (A ∩ D).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
  have hr : (A ∩ D).card ≤ D.card := Finset.card_le_card Finset.inter_subset_right
  rw [cut_halves_exact]
  change A.card + D.card = (A ∆ D).card + 2*(A ∩ D).card
  rw [hUnion,Finset.card_union_of_disjoint hd,Finset.card_sdiff,Finset.card_sdiff,
    Finset.inter_comm D A]
  omega

theorem overlap_bounded_by_backbone_both_sides (f : Vertices n → Bool) (hf : cutSize f≤n) :
    overlap f ≤ min (rightSide f).card (n-(rightSide f).card) := by
  have hl : overlap f ≤ (leftSide f).card := Finset.card_le_card Finset.inter_subset_left
  have hr : overlap f ≤ (rightSide f).card := Finset.card_le_card Finset.inter_subset_right
  rw [cut_halves_exact] at hf
  exact le_min hr (by omega)

def BackboneExpansion (B : SimpleGraph (Fin n)) (γ : ℚ) : Prop :=
  ∀ f : Fin n → Bool, γ * (↑(min (side f).card (n-(side f).card)) : ℚ) ≤
    (Nat.card (BackCross B f) : ℚ)

theorem actual_matching_backbone_cut (H B : SimpleGraph (Fin n)) (γ : ℚ)
    (hγ : 0≤γ) (hB : BackboneExpansion B γ) (f : Vertices n → Bool) (hf : cutSize f≤n) :
    (mismatch f : ℚ) + γ * ((cutSize f : ℚ)-(mismatch f : ℚ))/2 ≤
      (Nat.card (Crossing (ends H B) f) : ℚ) := by
  have hO : (overlap f : ℚ) ≤ (↑(min (rightSide f).card (n-(rightSide f).card)) : ℚ) := by
    exact_mod_cast overlap_bounded_by_backbone_both_sides f hf
  have hcross := (mul_le_mul_of_nonneg_left hO hγ).trans (hB (f ∘ Sum.inr))
  have ht : (cutSize f : ℚ) = (mismatch f : ℚ)+2*(overlap f : ℚ) := by
    exact_mod_cast cut_partition f
  have hsub : (cutSize f : ℚ)-(mismatch f : ℚ) = 2*(overlap f : ℚ) := by linarith
  rw [hsub,crossing_count,matching_crosses_exactly_symmDiff]
  push_cast
  linarith [show (0 : ℚ) ≤ (Nat.card (BackCross H (f ∘ Sum.inl)) : ℚ) by positivity]

theorem actual_half_cut_expansion (H B : SimpleGraph (Fin n)) (γ : ℚ)
    (hγ : 0≤γ) (hB : BackboneExpansion B γ) (f : Vertices n → Bool) (hf : cutSize f≤n) :
    min 1 (γ/2) * (cutSize f : ℚ) ≤ (Nat.card (Crossing (ends H B) f) : ℚ) := by
  let μ := min (1:ℚ) (γ/2)
  have hpart : (cutSize f : ℚ) = (mismatch f : ℚ)+2*(overlap f : ℚ) := by
    exact_mod_cast cut_partition f
  have hlarge : 0 ≤ (cutSize f : ℚ)-(mismatch f : ℚ) := by
    rw [hpart,add_sub_cancel_left]
    positivity
  have h1 : μ * (mismatch f : ℚ) ≤ (mismatch f : ℚ) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (min_le_left (1:ℚ) (γ/2)) (by positivity : (0:ℚ)≤(mismatch f : ℚ))
  have h2 : μ * ((cutSize f : ℚ)-(mismatch f : ℚ)) ≤
      γ/2*((cutSize f : ℚ)-(mismatch f : ℚ)) :=
    mul_le_mul_of_nonneg_right (min_le_right (1:ℚ) (γ/2)) hlarge
  calc
    μ * (cutSize f : ℚ) = μ*(mismatch f : ℚ)+μ*((cutSize f : ℚ)-(mismatch f : ℚ)) := by ring
    _ ≤ (mismatch f : ℚ)+γ/2*((cutSize f : ℚ)-(mismatch f : ℚ)) := add_le_add h1 h2
    _ = (mismatch f : ℚ)+γ*((cutSize f : ℚ)-(mismatch f : ℚ))/2 := by ring
    _ ≤ _ := actual_matching_backbone_cut H B γ hγ hB f hf

def oppositeCut {A : Type*} (f : A → Bool) (x : A) : Bool := !(f x)

theorem cut_complement_card (f : Vertices n → Bool) :
    cutSize f+cutSize (oppositeCut f)=2*n := by
  have hs : side (oppositeCut f) = (side f)ᶜ := by
    ext x
    simp only [side,oppositeCut,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl]
    cases f x <;> decide
  rw [cutSize,cutSize,card_filter_subtype,card_filter_subtype]
  change (side f).card+(side (oppositeCut f)).card=2*n
  rw [hs,Finset.card_add_card_compl,joined_vertices_card]

theorem same_edges_after_cut_complement (H B : SimpleGraph (Fin n)) (f : Vertices n → Bool) :
    Nat.card (Crossing (ends H B) (oppositeCut f)) = Nat.card (Crossing (ends H B) f) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.refl _) (fun e => ?_)
  simp only [Equiv.refl_apply,oppositeCut]
  cases f (ends H B e false) <;> cases f (ends H B e true) <;> decide

theorem actual_ambient_expansion (H B : SimpleGraph (Fin n)) (γ : ℚ)
    (hγ : 0≤γ) (hB : BackboneExpansion B γ) (f : Vertices n → Bool) :
    min 1 (γ/2) * (↑(min (cutSize f) (cutSize (oppositeCut f))) : ℚ) ≤
      (Nat.card (Crossing (ends H B) f) : ℚ) := by
  have sz := cut_complement_card f
  by_cases hf : cutSize f≤n
  · rw [min_eq_left (show cutSize f≤cutSize (oppositeCut f) by omega)]
    exact actual_half_cut_expansion H B γ hγ hB f hf
  · rw [min_eq_right (show cutSize (oppositeCut f)≤cutSize f by omega),
      ← same_edges_after_cut_complement H B f]
    exact actual_half_cut_expansion H B γ hγ hB (oppositeCut f) (by omega)

#print axioms crossing_equiv
#print axioms crossing_count
#print axioms cut_halves_exact
#print axioms matching_crosses_exactly_symmDiff
#print axioms cut_partition
#print axioms overlap_bounded_by_backbone_both_sides
#print axioms actual_matching_backbone_cut
#print axioms actual_half_cut_expansion
#print axioms cut_complement_card
#print axioms same_edges_after_cut_complement
#print axioms actual_ambient_expansion
end F5R60.Ambient
