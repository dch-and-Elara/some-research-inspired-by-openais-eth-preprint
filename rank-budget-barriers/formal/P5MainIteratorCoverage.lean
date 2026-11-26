import P5MainIteratorMarkov

/-! From uniform bad cells to the actual nonuniform source occupancies,
then to whole variables whose every incidence is good. -/
namespace P5MainIterator
open scoped BigOperators Classical

variable {E V F Copy I B : Type*} [Fintype E] [Fintype V]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def badIncidences (L : SourceLayout E V F Copy I B) : Finset E :=
  Finset.univ.filter (fun e => (L.placement.slot e).2 ∈ badCells I B)

noncomputable def cleanVariables (L : SourceLayout E V F Copy I B) : Finset V :=
  Finset.univ \ (badIncidences L).image L.placement.owner

omit [Fintype V] [Fintype Copy] in
theorem badIncidence_exact (L : SourceLayout E V F Copy I B) :
    (badIncidences L).card = ∑ u∈badCells I B,cellLoad L u := by
  unfold badIncidences cellLoad
  exact (Finset.sum_card_fiberwise_eq_card_filter Finset.univ (badCells I B)
    (fun e => (L.placement.slot e).2)).symm

omit [Fintype V] [Fintype Copy] in
theorem badIncidence_bound (L : SourceLayout E V F Copy I B) (hr : 2≤Fintype.card B)
    (hcap : ∀ u, cellLoad L u * Fintype.card (WordCell I B) ≤ 2*Fintype.card E) :
    ((badIncidences L).card:ℝ) ≤
      2*(Fintype.card E:ℝ)*(markBase*(3/4:ℝ))^Fintype.card I := by
  haveI : Nonempty B := Fintype.card_pos_iff.mp (by omega)
  have hD : 0<(Fintype.card (WordCell I B):ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card (WordCell I B))
  have hcap' (u : WordCell I B) :
      (cellLoad L u:ℝ) ≤ 2*(Fintype.card E:ℝ)/(Fintype.card (WordCell I B):ℝ) := by
    apply (le_div_iff₀ hD).mpr
    exact_mod_cast hcap u
  calc
    _ = ∑ u∈badCells I B,(cellLoad L u:ℝ) := by rw [badIncidence_exact,Nat.cast_sum]
    _ ≤ ∑ _u∈badCells I B,2*(Fintype.card E:ℝ)/(Fintype.card (WordCell I B):ℝ) :=
      Finset.sum_le_sum (fun u _ => hcap' u)
    _ = ((badCells I B).card:ℝ)*(2*(Fintype.card E:ℝ)/(Fintype.card (WordCell I B):ℝ)) := by simp
    _ ≤ ((Fintype.card (WordCell I B):ℝ)*(markBase*(3/4:ℝ))^Fintype.card I) *
        (2*(Fintype.card E:ℝ)/(Fintype.card (WordCell I B):ℝ)) :=
      mul_le_mul_of_nonneg_right (bad_cells_count hr) (by positivity)
    _ = _ := by field_simp

omit [Fintype Copy] in
theorem clean_variables_count (L : SourceLayout E V F Copy I B) :
    Fintype.card V ≤ (cleanVariables L).card+(badIncidences L).card := by
  have hh := Finset.le_card_sdiff ((badIncidences L).image L.placement.owner) (Finset.univ : Finset V)
  have H : ((badIncidences L).image L.placement.owner).card≤(badIncidences L).card :=
    Finset.card_image_le
  simp only [Finset.card_univ] at hh
  dsimp [cleanVariables]
  omega

omit [Fintype Copy] in
theorem every_clean_occurrence_good (L : SourceLayout E V F Copy I B) {v : V}
    (hv : v ∈ cleanVariables L) {e : E} (he : e∈incidences L.placement v) :
    e∉badIncidences L := by
  have hx := (Finset.mem_sdiff.mp hv).2
  intro h
  exact hx (Finset.mem_image.mpr ⟨e,h,(Finset.mem_filter.mp he).2⟩)

set_option maxHeartbeats 5000000 in
theorem actual_FA3_of_escape (L : SourceLayout E V F Copy I B) (t : I)
    (keep : ℕ → Prop) (p : ℝ) (hp : 0≤p) (hr : 2≤Fintype.card B)
    (hcap : ∀ u, cellLoad L u * Fintype.card (WordCell I B) ≤ 2*Fintype.card E)
    (hhalf : 2*(Fintype.card E:ℝ)*(markBase*(3/4:ℝ))^Fintype.card I ≤ (Fintype.card V:ℝ)/2)
    (hpoint : ∀ n≤Fintype.card I, Fintype.card I≤4*n → p≤binomialMass n keep) :
    ((Fintype.card V:ℝ)/2)*p ≤
      Real.log ((Set.range (sourceTuple keep L t)).ncard : ℝ) / Real.log 2 := by
  let term (v : V) := (∑ e∈incidences L.placement v, binomialMass (activeCount (L.placement.slot e).2) keep) /
      (incidences L.placement v).card
  have hp' (v : V) : 0≤term v := by
    dsimp [term]
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => by unfold binomialMass; positivity)) (by positivity)
  have hn (v : V) (hv : v∈cleanVariables L) : p≤term v := by
    have H : 0<(incidences L.placement v).card := by rw [←filled_card]; exact filled_pos _ _
    dsimp [term]
    apply (le_div_iff₀ (by exact_mod_cast H)).mpr
    rw [mul_comm]
    calc
      _ = ∑ _e∈incidences L.placement v,p := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro e he
        apply hpoint
        · unfold activeCount
          exact Fintype.card_subtype_le _
        · by_contra! h
          exact every_clean_occurrence_good L hv he
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩)
  have good_card : (Fintype.card V:ℝ)/2≤(cleanVariables L).card := by
    have hg := (badIncidence_bound L hr hcap).trans hhalf
    have h : (Fintype.card V:ℝ)≤(cleanVariables L).card+(badIncidences L).card := by
      exact_mod_cast clean_variables_count L
    linarith only [hg,h]
  have hFA := finite_FA1 keep L t
  calc
    _ ≤ ((cleanVariables L).card:ℝ)*p := mul_le_mul_of_nonneg_right good_card hp
    _ = ∑ _v∈cleanVariables L,p := by simp
    _ ≤ ∑ v∈cleanVariables L,term v := Finset.sum_le_sum hn
    _ ≤ ∑ v : V,term v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hp' v)
    _ ≤ _ := hFA.1.trans hFA.2

#print axioms badIncidence_exact
#print axioms badIncidence_bound
#print axioms clean_variables_count
#print axioms every_clean_occurrence_good
#print axioms actual_FA3_of_escape
end P5MainIterator
