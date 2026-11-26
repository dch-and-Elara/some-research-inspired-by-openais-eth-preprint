import S6Placement
import S6Fair

namespace Section6

open Finset
open scoped BigOperators
set_option linter.unusedSectionVars false

noncomputable section

abbrev cubeSize (I A : Type*) [Fintype I] [DecidableEq I] [Fintype A] :=
  Fintype.card (WordCell I A)

lemma cubeSize_eq (I A : Type*) [Fintype I] [DecidableEq I] [Fintype A] :
    cubeSize I A = (Fintype.card A) ^ (2 * Fintype.card I) := by
  simp [cubeSize, pow_mul, pow_two]

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [LinearOrder A]

def lightCells : Finset (WordCell I A) :=
  univ.filter fun u => 4 * (unequal u).card < Fintype.card I

def rootTwo : ℝ := √(√(2 : ℝ))
def xi : ℝ := rootTwo * (3 / 4)

lemma rootTwo_pow : rootTwo ^ 4 = 2 := by
  unfold rootTwo
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul,
    Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]

lemma rootTwo_pos : 0 < rootTwo := by unfold rootTwo; positivity

lemma rootTwo_ge_one : 1 ≤ rootTwo := by
  by_contra! h
  have := pow_lt_pow_left₀ h rootTwo_pos.le (by decide : 4 ≠ 0)
  rw [rootTwo_pow] at this
  norm_num at this

lemma xi_lt_one : xi < 1 := by
  by_contra! h
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h 4
  unfold xi at hp
  rw [mul_pow, rootTwo_pow] at hp
  norm_num at hp

def pairMass (u : A × A) : ℝ := 1/2 + if u.1 = u.2 then 1/2 else 0

lemma cellMass (u : WordCell I A) :
    ∏ i, pairMass (u i) = (1 / 2 : ℝ) ^ (unequal u).card := by
  unfold unequal
  rw [← prod_const, prod_filter]
  apply prod_congr rfl
  intro i _
  by_cases h : (u i).1 = (u i).2 <;> norm_num [pairMass, h]

lemma pairMass_sum (hr : 2 ≤ Fintype.card A) :
    ∑ u : A × A, pairMass u ≤ (Fintype.card (A × A) : ℝ) * (3 / 4) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [pairMass, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq, mem_univ, if_true,
    Fintype.card_prod, Nat.cast_mul]
  have h : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hr
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (show (0 : ℝ) ≤ Fintype.card A by positivity)]

/-- The Markov estimate on all full cells, uniformly in r >= 2. -/
theorem light_cell_count (hr : 2 ≤ Fintype.card A) :
    ((lightCells (I := I) (A := A)).card : ℝ) ≤ (cubeSize I A : ℝ) * xi ^ Fintype.card I := by
  classical
  let light : Finset (WordCell I A) := lightCells
  let m (u : WordCell I A) := ∏ i, pairMass (u i)
  have hmass (u : WordCell I A) : 0 ≤ m u := by rw [show m u = _ from cellMass u]; positivity
  have hunit (u : WordCell I A) (hu : u ∈ light) :
      1 ≤ rootTwo ^ Fintype.card I * m u := by
    have h : 4 * (unequal u).card ≤ Fintype.card I := by
      exact (mem_filter.mp hu).2.le
    rw [show m u = _ from cellMass u, one_div, inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (unequal u).card)).mpr
    rw [one_mul, ← rootTwo_pow, ← pow_mul]
    exact pow_le_pow_right₀ rootTwo_ge_one h
  calc
    (light.card : ℝ) = ∑ _ ∈ light, (1 : ℝ) := by simp
    _ ≤ ∑ u ∈ light, rootTwo ^ Fintype.card I * m u := sum_le_sum hunit
    _ ≤ ∑ u : WordCell I A, rootTwo ^ Fintype.card I * m u :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun u _ _ =>
        mul_nonneg (pow_nonneg rootTwo_pos.le _) (hmass u))
    _ = rootTwo ^ Fintype.card I * (∑ u : WordCell I A, m u) := (mul_sum ..).symm
    _ = rootTwo ^ Fintype.card I * (∑ u : A × A, pairMass u) ^ Fintype.card I := by
      unfold m
      rw [← Fintype.prod_sum (fun _ : I => pairMass), prod_const, card_univ]
    _ ≤ rootTwo ^ Fintype.card I * ((Fintype.card (A × A) : ℝ) * (3 / 4)) ^ Fintype.card I :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun u _ => by unfold pairMass; positivity)
        (pairMass_sum hr) _) (pow_nonneg rootTwo_pos.le _)
    _ = _ := by
      rw [xi, mul_pow, mul_pow]
      simp [cubeSize, Fintype.card_pi]
      ring

variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

def occupied (P : Placement V H I A) : Finset (H × WordCell I A) :=
  univ.filter fun x => (P.owner x).isSome

def loadCell (P : Placement V H I A) (u : WordCell I A) : ℕ :=
  ((occupied P).filter (fun x => x.2 = u)).card

def badPlaces (P : Placement V H I A) : Finset (H × WordCell I A) :=
  (occupied P).filter fun x => x.2 ∈ (lightCells (I := I) (A := A))

def badVars (P : Placement V H I A) : Finset V := by
  classical
  exact univ.filter fun v => ∃ x ∈ badPlaces P, P.owner x = some v

lemma badVars_count_le (P : Placement V H I A) :
    (badVars P).card ≤ (badPlaces P).card := by
  classical
  have hex (v : V) (hv : v ∈ badVars P) : ∃ x ∈ badPlaces P, P.owner x = some v :=
    (mem_filter.mp hv).2
  let f (v : {v // v ∈ badVars P}) : {x // x ∈ badPlaces P} :=
    ⟨(hex v.val v.property).choose, (hex v.val v.property).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro v w h
    have he := congrArg (fun x : {x // x ∈ badPlaces P} => P.owner x.val) h
    change P.owner (hex v.val v.property).choose = P.owner (hex w.val w.property).choose at he
    rw [(hex v.val v.property).choose_spec.2, (hex w.val w.property).choose_spec.2] at he
    exact Subtype.ext (Option.some.inj he)
  simpa [Fintype.card_coe] using Fintype.card_le_of_injective f hf

lemma badPlaces_count_le (P : Placement V H I A) (hr : 2 ≤ Fintype.card A)
    (hcap : ∀ u, (loadCell P u : ℝ) * cubeSize I A ≤ 2 * (occupied P).card) :
    ((badPlaces P).card : ℝ) ≤ 2 * (occupied P).card * xi ^ Fintype.card I := by
  classical
  have hD : 0 < (cubeSize I A : ℝ) := by
    rw [cubeSize_eq]
    have h : 0 < (Fintype.card A : ℝ) := by exact_mod_cast (show 0 < Fintype.card A by omega)
    positivity
  have he : (badPlaces P).card = ∑ u ∈ lightCells, loadCell P u := by
    rw [badPlaces, ← sum_card_fiberwise_eq_card_filter]
    rfl
  rw [he, Nat.cast_sum]
  calc
    _ ≤ ∑ _u ∈ (lightCells (I := I) (A := A)), 2 * ((occupied P).card : ℝ) / cubeSize I A :=
      sum_le_sum fun u _ => (le_div_iff₀ hD).mpr (hcap u)
    _ = ((lightCells (I := I) (A := A)).card : ℝ) * (2 * (occupied P).card / cubeSize I A) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ ((cubeSize I A : ℝ) * xi ^ Fintype.card I) * (2 * (occupied P).card / cubeSize I A) :=
      mul_le_mul_of_nonneg_right (light_cell_count hr) (by positivity)
    _ = _ := by field_simp

/-- F.A3 on the actual matrix. The displayed cardinal bound in F.A1 gives the
paper's logarithm at every node from this rank bound. -/
theorem FA3 (P : Placement V H I A) (window : Finset ℕ) (R : ℕ)
    (hr : 2 ≤ Fintype.card A) (hQ : 256 ≤ Fintype.card I) (hw : window.card = R)
    (hR : 16 * R ≤ Fintype.card I)
    (hcap : ∀ u, (loadCell P u : ℝ) * cubeSize I A ≤ 2 * (occupied P).card)
    (hdensity : 2 * (occupied P).card * xi ^ Fintype.card I ≤ (Fintype.card V : ℝ) / 2) :
    (Real.exp (-16) / 16) * (Fintype.card V : ℝ) *
        Real.exp (-(64 * (R : ℝ)^2 / Fintype.card I)) ≤ (actualMatrix P window).rank := by
  classical
  let c := (Real.exp (-16) / 8) * Real.exp (-(64 * (R : ℝ)^2 / Fintype.card I))
  let good : Finset V := univ \ badVars P
  have hgood : (Fintype.card V : ℝ) / 2 ≤ (good.card : ℝ) := by
    have hbad := (show ((badVars P).card : ℝ) ≤ (badPlaces P).card by exact_mod_cast badVars_count_le P)
      |>.trans (badPlaces_count_le P hr hcap) |>.trans hdensity
    have hsum : good.card + (badVars P).card = Fintype.card V := by
      simpa [good] using card_sdiff_add_card_eq_card (subset_univ (badVars P))
    have hsum' : (good.card : ℝ) + (badVars P).card = Fintype.card V := by exact_mod_cast hsum
    linarith
  let mass (v : V) : ℝ :=
    (∑ x ∈ occurrences P v, (fairTail (unequal x.2).card window : ℝ)) / (occurrences P v).card
  have hmass (v : V) : 0 ≤ mass v := by
    have ht (k : ℕ) : 0 ≤ (fairTail k window : ℝ) := by
      rw [fairTail_cast]
      exact sum_nonneg fun j _ => fairMass_nonneg _ _
    exact div_nonneg (sum_nonneg fun x _ => ht (unequal x.2).card) (by positivity)
  have hgoodMass (v : V) (hv : v ∈ good) : c ≤ mass v := by
    have hb : v ∉ badVars P := (mem_sdiff.mp hv).2
    have hp : 0 < ((occurrences P v).card : ℝ) := by
      obtain ⟨x, hx⟩ := P.occurs v
      exact_mod_cast (card_pos.mpr ⟨x, by simp [occurrences, hx]⟩ :
        0 < (occurrences P v).card)
    apply (le_div_iff₀ hp).mpr
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro x hx
    have howner : P.owner x = some v := (mem_filter.mp hx).2
    have hlight : ¬x.2 ∈ (lightCells (I := I) (A := A)) := by
      intro hh
      apply hb
      simpa only [badVars, mem_filter, mem_univ, true_and] using
        (show ∃ x ∈ badPlaces P, P.owner x = some v from
          ⟨x, mem_filter.mpr ⟨by simp [occupied, howner], hh⟩, howner⟩)
    have hunequal : Fintype.card I ≤ 4 * (unequal x.2).card := by
      simpa [lightCells] using hlight
    exact FA2 (Fintype.card I) (unequal x.2).card R window hQ hunequal
      (by simpa using card_le_card (subset_univ (unequal x.2))) hR hw
  have hrank : ∑ v, mass v ≤ ((actualMatrix P window).rank : ℝ) := by
    have hrank' := (show (↑(∑ v, (∑ x ∈ occurrences P v, fairTail (unequal x.2).card window) /
          ((occurrences P v).card : ℚ)) : ℝ) ≤ (((actualMatrix P window).rank : ℚ) : ℝ)
      from (Rat.cast_le (K := ℝ)).mpr (projection_trace_rank P window))
    push_cast at hrank'
    exact hrank'
  calc
    _ = (Fintype.card V : ℝ) / 2 * c := by unfold c; ring
    _ ≤ (good.card : ℝ) * c := mul_le_mul_of_nonneg_right hgood (by unfold c; positivity)
    _ = ∑ _v ∈ good, c := by simp
    _ ≤ ∑ v ∈ good, mass v := sum_le_sum hgoodMass
    _ ≤ ∑ v, mass v := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v _ _ => hmass v)
    _ ≤ _ := hrank

#print axioms light_cell_count
#print axioms badPlaces_count_le
#print axioms badVars_count_le
#print axioms FA3

end
end Section6





