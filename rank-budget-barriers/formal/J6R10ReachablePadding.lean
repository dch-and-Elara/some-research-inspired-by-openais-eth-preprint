import J6RecursiveMenu
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

/-! A finite mode alphabet may be enlarged without adding even a single
legal tuple. Give every new dummy label weight at least the local
precision. Its exponent is then forced to zero by the printed strict
budget. The actual menu and complete child sum reindex exactly. -/
namespace J6R10Reachable
open scoped BigOperators
open J6RecursiveMenu

variable {I J : Type*}

noncomputable def paddedWeight (p : ℕ) (e : I ↪ J) (w : I → ℕ) (j : J) : ℕ := by
  classical
  exact if h : j ∈ Set.range e then w (Classical.choose h) else p

theorem paddedWeight_hit (p : ℕ) (e : I ↪ J) (w : I → ℕ) (i : I) :
    paddedWeight p e w (e i) = w i := by
  classical
  let h : e i ∈ Set.range e := ⟨i,rfl⟩
  unfold paddedWeight
  rw [dif_pos h]
  exact congrArg w (e.injective (Classical.choose_spec h))

theorem paddedWeight_miss (p : ℕ) (e : I ↪ J) (w : I → ℕ)
    (j : J) (hj : j ∉ Set.range e) : paddedWeight p e w j = p := by
  classical
  simp [paddedWeight,hj]

theorem ambient_positive (p : ℕ) (hp : 0 < p) (e : I ↪ J) (w : I → ℕ)
    (W : J → ℕ) (hw : ∀ i, 0 < w i) (hW : ∀ i, W (e i) = w i)
    (hDummy : ∀ j ∉ Set.range e, p ≤ W j) (j : J) : 0 < W j := by
  by_cases h : j ∈ Set.range e
  · obtain ⟨i,rfl⟩ := h
    rw [hW i]
    exact hw i
  · exact hp.trans_le (hDummy j h)

variable [Fintype J]

theorem phantom_exponent_zero (p : ℕ) (W : J → ℕ) (β : J →₀ ℕ)
    (h : weighted W β < p) (j : J) (hj : p ≤ W j) : β j = 0 := by
  by_contra hn
  have hb : 1 ≤ β j := Nat.pos_of_ne_zero hn
  have hle : W j * β j ≤ weighted W β :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (W i * β i)) (Finset.mem_univ j)
  have hd : W j ≤ W j * β j := by simpa using Nat.mul_le_mul_left (W j) hb
  exact (not_lt_of_ge (hj.trans (hd.trans hle))) h

variable [Fintype I]

theorem weighted_embDomain (e : I ↪ J) (w : I → ℕ) (W : J → ℕ)
    (hW : ∀ i, W (e i) = w i) (β : I →₀ ℕ) :
    weighted W (Finsupp.embDomain e β) = weighted w β := by
  classical
  unfold weighted
  calc
    _ = ∑ j ∈ Finset.univ.map e, W j * Finsupp.embDomain e β j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hn : j ∉ Set.range e := by
        rintro ⟨i,rfl⟩
        exact hj (Finset.mem_map.mpr ⟨i,Finset.mem_univ i,rfl⟩)
      rw [Finsupp.embDomain_notin_range e β j hn,mul_zero]
    _ = _ := by
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl (fun i _ => by rw [Finsupp.embDomain_apply,hW i])

noncomputable def modeEmbedding (e : I ↪ J) : (I →₀ ℕ) ↪ (J →₀ ℕ) :=
  ⟨Finsupp.embDomain e,Finsupp.embDomain_injective e⟩

variable [DecidableEq I] [DecidableEq J]

/-- This equality is equality of finite menus as sets with the exact
multiplicities implicit in an injective mapping, not a cardinal bound. -/
theorem ambient_menu (p : ℕ) (hp : 0 < p) (e : I ↪ J) (w : I → ℕ)
    (W : J → ℕ) (hw : ∀ i, 0 < w i) (hW : ∀ i, W (e i) = w i)
    (hDummy : ∀ j ∉ Set.range e, p ≤ W j) :
    (menu p w).map (modeEmbedding e) = menu p W := by
  classical
  have hpos := ambient_positive p hp e w W hw hW hDummy
  ext β
  rw [Finset.mem_map,exact_printed_menu p W hpos]
  constructor
  · rintro ⟨a,ha,rfl⟩
    change weighted W (Finsupp.embDomain e a) < p
    rw [weighted_embDomain e w W hW]
    exact (exact_printed_menu p w hw _).mp ha
  · intro hb
    have hs : ↑β.support ⊆ Set.range e := by
      intro j hj
      by_contra hn
      have hz := phantom_exponent_zero p W β hb j (hDummy j hn)
      exact Finsupp.notMem_support_iff.mpr hz hj
    let a := Finsupp.comapDomain e β e.injective.injOn
    have he : Finsupp.embDomain e a = β := Finsupp.embDomain_comapDomain hs
    refine ⟨a,(exact_printed_menu p w hw _).mpr ?_,he⟩
    rw [← weighted_embDomain e w W hW a,he]
    exact hb

theorem padded_menu (p : ℕ) (hp : 0 < p) (e : I ↪ J) (w : I → ℕ)
    (hw : ∀ i, 0 < w i) :
    (menu p w).map (modeEmbedding e) = menu p (paddedWeight p e w) :=
  ambient_menu p hp e w _ hw (paddedWeight_hit p e w)
    (fun j hj => le_of_eq (paddedWeight_miss p e w j hj).symm)

abbrev Menu {I : Type*} [Fintype I] [DecidableEq I] (p : ℕ) (w : I → ℕ) :=
  {β : I →₀ ℕ // β ∈ menu p w}

/-- Actual bijection for the subtype-indexed mode slots of R9. -/
noncomputable def menuEquiv (p : ℕ) (hp : 0 < p) (e : I ↪ J) (w : I → ℕ)
    (hw : ∀ i, 0 < w i) : Menu p w ≃ Menu p (paddedWeight p e w) :=
  Equiv.ofBijective (fun β =>
    ⟨Finsupp.embDomain e β.val, by
      rw [← padded_menu p hp e w hw]
      exact Finset.mem_map.mpr ⟨β.val,β.property,rfl⟩⟩) (by
    constructor
    · intro β γ h
      exact Subtype.ext (Finsupp.embDomain_injective e (congrArg Subtype.val h))
    · intro β
      have hb : β.val ∈ (menu p w).map (modeEmbedding e) :=
        (congrArg (fun t => β.val ∈ t) (padded_menu p hp e w hw)).mpr β.property
      obtain ⟨γ,hγ,hEq⟩ := Finset.mem_map.mp hb
      exact ⟨⟨γ,hγ⟩,Subtype.ext hEq⟩)

theorem menuEquiv_val (p : ℕ) (hp : 0 < p) (e : I ↪ J) (w : I → ℕ)
    (hw : ∀ i, 0 < w i) (β : menu p w) :
    (menuEquiv p hp e w hw β).val = Finsupp.embDomain e β.val := rfl

/-- Exact reindexing of the recursive mode sum (including every group),
valid over the finite receiving rings, not only characteristic zero. -/
theorem group_sum_pad {G R : Type*} [Fintype G] [CommSemiring R]
    (p : ℕ) (hp : 0 < p) (e : I ↪ J) (w : I → ℕ) (hw : ∀ i, 0 < w i)
    (native : (I →₀ ℕ) → G → R) (wide : (J →₀ ℕ) → G → R)
    (agree : ∀ β ∈ menu p w, ∀ g, wide (Finsupp.embDomain e β) g = native β g) :
    (∑ β ∈ menu p (paddedWeight p e w), ∏ g, wide β g) =
      ∑ β ∈ menu p w, ∏ g, native β g := by
  rw [← padded_menu p hp e w hw,Finset.sum_map]
  refine Finset.sum_congr rfl (fun β hβ => Finset.prod_congr rfl (fun g _ => ?_))
  exact agree β hβ g

/-- Reindexing in exactly the dependent subtype form of the R9 binder. -/
theorem group_sum_pad_subtype {G R : Type*} [Fintype G] [CommSemiring R]
    (p : ℕ) (hp : 0 < p) (e : I ↪ J) (w : I → ℕ) (hw : ∀ i, 0 < w i)
    (native : Menu p w → G → R)
    (wide : Menu p (paddedWeight p e w) → G → R)
    (agree : ∀ β g, wide (menuEquiv p hp e w hw β) g = native β g) :
    (∑ β : Menu p (paddedWeight p e w), ∏ g, wide β g) =
      ∑ β : Menu p w, ∏ g, native β g := by
  symm
  apply Fintype.sum_equiv (menuEquiv p hp e w hw)
  intro β
  exact Finset.prod_congr rfl (fun g _ => (agree β g).symm)

#print axioms menuEquiv_val
#print axioms group_sum_pad_subtype
#print axioms paddedWeight_hit
#print axioms paddedWeight_miss
#print axioms ambient_positive
#print axioms phantom_exponent_zero
#print axioms weighted_embDomain
#print axioms ambient_menu
#print axioms padded_menu
#print axioms group_sum_pad
end J6R10Reachable