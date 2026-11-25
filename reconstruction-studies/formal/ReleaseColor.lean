import ColorAlphabetTensor
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.Abel

open scoped BigOperators Polynomial
open Reconstruction.ColorAlphabet

namespace Reconstruction.ReleaseColor

noncomputable section

variable {L R G F : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [AddCommGroup G] [Fintype G] [DecidableEq G] [Field F]

/-- The coordinate functional on one physical file/function pair. -/
def coordinateRow (u : L × L) (v : L × L) : F := if u = v then 1 else 0

/-- The locally known coordinates are all the columns whose first letter is b. -/
def sideSpan (b : L) : Submodule F (L × L → F) :=
  Submodule.span F (Set.range (fun c : L => coordinateRow (F := F) (b,c)))

def translated (colors : Finset G) (h g : G) : Prop := g - h ∈ colors

instance (colors : Finset G) (h : G) : DecidablePred (translated colors h) :=
  fun _ => inferInstanceAs (Decidable (_ ∈ colors))

/-- The genuine span of the basis rows in the chosen translate. -/
def translateSpan (B : Module.Basis R F (L × L → F)) (color : R → G)
    (colors : Finset G) (h : G) : Submodule F (L × L → F) :=
  Submodule.span F
    (Set.range (fun k : {k : R // translated colors h (color k)} => B k.val))

def SufficientTranslates (B : Module.Basis R F (L × L → F)) (color : R → G)
    (colors : Finset G) : Prop :=
  ∀ (h : G) (u : L × L), coordinateRow u ∈ translateSpan B color colors h ⊔ sideSpan u.2

def encoder (B : Module.Basis R F (L × L → F)) (color : R → G)
    (colors : Finset G) (h : G) (q : ℕ) :
    Matrix (ColorRows q color (translated colors h)) (Word (fun _ : Fin q => L)) F :=
  tensorRows (fun k => B k) q color (translated colors h)

omit [Fintype L] [Fintype R] [DecidableEq R] [Fintype G] in
private theorem sideSpan_zero {b : L} {v : L × L} (hv : v.1 ≠ b)
    {s : L × L → F} (hs : s ∈ sideSpan b) : s v = 0 := by
  let ev : (L × L → F) →ₗ[F] F := LinearMap.proj v
  apply (Submodule.span_le.2 ?_ : sideSpan b ≤ LinearMap.ker ev) hs
  rintro _ ⟨c, rfl⟩
  change coordinateRow (b,c) v = 0
  exact if_neg (fun h => hv (congrArg Prod.fst h).symm)

omit [Fintype L] [DecidableEq R] [Fintype G] in
private theorem decode_translate (B : Module.Basis R F (L × L → F)) (color : R → G)
    (colors : Finset G) (h₀ : G) (hS : SufficientTranslates B color colors)
    (g : G) (u : L × L) :
    ∃ d : R → F, (∀ k, ¬ translated colors h₀ (color k + g) → d k = 0) ∧
      ∀ v, v.1 ≠ u.2 → ∑ k, d k * B k v = if u = v then 1 else 0 := by
  classical
  let h := h₀ - g
  let I := {k : R // translated colors h (color k)}
  obtain ⟨m, hm, s, hs, hms⟩ := Submodule.mem_sup.mp (hS h u)
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  change (c : I →₀ F).sum (fun k a => a • B k.val) = m at hc
  let d (k : R) : F := if hk : translated colors h (color k) then c ⟨k,hk⟩ else 0
  have hspan : ∑ k, d k • B k = m := by
    rw [← hc, Finsupp.sum_fintype c (fun (k : I) (a : F) => a • B k.val)
      (fun _ => zero_smul F _)]
    calc
      _ = ∑ k ∈ Finset.univ.filter (fun k : R => translated colors h (color k)), d k • B k := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : translated colors h (color k) <;> simp [d, hk]
      _ = ∑ k : I, d k.val • B k.val := Finset.sum_subtype _ (by simp) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        simp [d, k.property]
  refine ⟨d, ?_, ?_⟩
  · intro k hk
    apply dif_neg
    intro he
    apply hk
    change color k + g - h₀ ∈ colors
    have heq : color k + g - h₀ = color k - h := by dsimp [h]; abel
    rw [heq]
    exact he
  · intro v hv
    have h := congrArg (fun f : L × L → F => f v) (hspan.symm.trans rfl)
    have h' := congrArg (fun f : L × L → F => f v) hms
    change m v + s v = coordinateRow u v at h'
    rw [sideSpan_zero hv hs, add_zero] at h'
    change (∑ k, d k * B k v) = coordinateRow u v
    rw [← h']
    simpa [Finset.sum_apply, smul_eq_mul] using h.symm

omit [Fintype G] in
theorem encoder_recovers (B : Module.Basis R F (L × L → F)) (color : R → G)
    (colors : Finset G) (h : G) (q : ℕ) (hS : SufficientTranslates B color colors) :
    Recovers (encoder B color colors h q) := by
  apply tensorRows_recovers
  · intro u
    refine ⟨fun k => (B.repr (coordinateRow u)) k, fun v => ?_⟩
    have he := congrArg (fun f : L × L → F => f v) (B.sum_repr (coordinateRow u))
    simpa [Finset.sum_apply, smul_eq_mul, coordinateRow] using he
  · exact decode_translate B color colors h hS

omit [Fintype R] [DecidableEq R] [Fintype G] [DecidableEq G] in
private theorem slot_pair (B : Module.Basis R F (L × L → F)) (k j : R) [DecidableEq R] :
    (∑ v : L × L, B k v * (B.repr (coordinateRow v)) j) = if k = j then 1 else 0 := by
  classical
  have he : (∑ v : L × L, B k v • coordinateRow (F := F) v) = B k := by
    funext w
    simp [coordinateRow, Finset.sum_apply, smul_eq_mul, mul_ite]
  have hp := congrArg (fun f : L × L → F => (B.repr f) j) he
  change (B.repr (∑ v : L × L, B k v • coordinateRow (F := F) v)) j = (B.repr (B k)) j at hp
  simpa [map_sum, Finsupp.finset_sum_apply, smul_eq_mul, Finsupp.single_apply, eq_comm] using hp

omit [Fintype R] [Fintype G] [DecidableEq G] in
private theorem tensor_pair (B : Module.Basis R F (L × L → F)) {q : ℕ}
    (k j : Fin q → R) :
    (∑ v : Word (fun _ : Fin q => L),
      (∏ i, B (k i) (v i)) * (∏ i, (B.repr (coordinateRow (v i))) (j i))) =
        if k = j then 1 else 0 := by
  classical
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin q) (v : L × L) =>
    B (k i) v * (B.repr (coordinateRow v)) (j i))]
  simp only [slot_pair]
  by_cases h : k = j
  · simp [h]
  · obtain ⟨i, hi⟩ : ∃ i, k i ≠ j i := by
      by_contra! h'
      exact h (funext h')
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).trans (if_neg h).symm

omit [Fintype G] [DecidableEq G] in
theorem tensor_basis_rank_card (B : Module.Basis R F (L × L → F)) (color : R → G)
    (accept : G → Prop) [DecidablePred accept] (q : ℕ) :
    (tensorRows (fun k => B k) q color accept).rank = Fintype.card (ColorRows q color accept) := by
  classical
  apply LinearIndependent.rank_matrix
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let du (v : Word (fun _ : Fin q => L)) : F :=
    ∏ i, (B.repr (coordinateRow (v i))) (j.val i)
  calc
    c j = ∑ k, c k * (if k = j then 1 else 0) := by simp [mul_ite]
    _ = ∑ k, c k * (∑ v, tensorRows (fun k => B k) q color accept k v * du v) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [show (∑ v, tensorRows (fun k => B k) q color accept k v * du v) =
        (if k.val = j.val then 1 else 0) from tensor_pair B k.val j.val]
      by_cases hk : k = j
      · simp [hk]
      · have hn : k.val ≠ j.val := fun he => hk (Subtype.ext he)
        rw [if_neg hk, if_neg hn]
    _ = 0 := by
      simp_rw [Finset.mul_sum, ← mul_assoc, Finset.sum_comm (f := fun k v =>
        c k * tensorRows (fun k => B k) q color accept k v * du v)]
      apply Finset.sum_eq_zero
      intro v _
      rw [← Finset.sum_mul]
      have hz := congrArg (fun f : Word (fun _ : Fin q => L) → F => f v) hc
      simp only [Matrix.row, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
      rw [hz, zero_mul]

omit [Fintype G] in
theorem encoder_rank_card (B : Module.Basis R F (L × L → F)) (color : R → G)
    (colors : Finset G) (h : G) (q : ℕ) :
    (encoder B color colors h q).rank = Fintype.card (ColorRows q color (translated colors h)) :=
  tensor_basis_rank_card B color (translated colors h) q

/-- The one-slot color multiplicity, including empty colors. -/
def colorMass (color : R → G) (g : G) : ℕ := Fintype.card {k : R // color k = g}

/-- Additive convolution power of the one-slot multiplicity. -/
def convolutionPower (mass : G → ℕ) : ℕ → G → ℕ
  | 0, g => if g = 0 then 1 else 0
  | q+1, g => ∑ x, mass x * convolutionPower mass q (g-x)

private abbrev Fiber (color : R → G) (q : ℕ) (g : G) :=
  {s : Fin q → R // totalColor color s = g}

omit [Fintype R] [DecidableEq R] [Fintype G] [DecidableEq G] in
private theorem color_cons (color : R → G) {q : ℕ} (k : R) (s : Fin q → R) :
    totalColor color (Fin.cons k s) = color k + totalColor color s := by
  simp [totalColor, Fin.sum_univ_succ]

private def splitFiber (color : R → G) (q : ℕ) (g : G) :
    (Σ k : R, Fiber color q (g - color k)) ≃ Fiber color (q+1) g where
  toFun p := ⟨Fin.cons p.1 p.2.val, by rw [color_cons,p.2.property]; abel⟩
  invFun s := ⟨s.val 0, ⟨Fin.tail s.val, by
    apply eq_sub_of_add_eq'
    rw [← color_cons, Fin.cons_self_tail]
    exact s.property⟩⟩
  left_inv := by rintro ⟨k,s⟩; simp
  right_inv s := Subtype.ext (Fin.cons_self_tail _)

theorem convolutionPower_card (color : R → G) (q : ℕ) (g : G) :
    Fintype.card (Fiber color q g) = convolutionPower (colorMass color) q g := by
  classical
  induction q generalizing g with
  | zero =>
    by_cases hg : g = 0
    · subst g
      let e : Fiber color 0 0 ≃ (Fin 0 → R) :=
        { toFun := Subtype.val
          invFun := fun s => ⟨s, by simp [totalColor]⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e]
      simp [convolutionPower]
    · letI : IsEmpty (Fiber color 0 g) :=
        ⟨fun s => hg (s.property.symm.trans (by simp [totalColor]))⟩
      simp [hg, convolutionPower]
  | succ q ih =>
    rw [← Fintype.card_congr (splitFiber color q g), Fintype.card_sigma, convolutionPower]
    simp_rw [ih]
    rw [← Finset.sum_fiberwise Finset.univ color
      (fun k => convolutionPower (colorMass color) q (g-color k))]
    apply Finset.sum_congr rfl
    intro x _
    rw [colorMass, Fintype.subtype_card]
    calc
      _ = ∑ _k ∈ Finset.univ.filter (fun k => color k = x),
          convolutionPower (colorMass color) q (g-x) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]

theorem selected_card (color : R → G) (colors : Finset G) (h : G) (q : ℕ) :
    Fintype.card (ColorRows q color (translated colors h)) =
      ∑ g ∈ Finset.univ.filter (translated colors h), convolutionPower (colorMass color) q g := by
  classical
  let e : (Σ g : {g // translated colors h g}, Fiber color q g.val) ≃
      ColorRows q color (translated colors h) :=
    { toFun := fun g => ⟨g.2.val, g.2.property.symm ▸ g.1.property⟩
      invFun := fun s => ⟨⟨totalColor color s.val, s.property⟩, ⟨s.val, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨g,hg⟩, ⟨s,hs⟩⟩
        change totalColor color s = g at hs
        subst g
        rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [convolutionPower_card]
  exact (Finset.sum_subtype _ (by simp) _).symm

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] [Fintype G] [DecidableEq G] in
theorem encoder_ternary (B : Module.Basis R ℚ (L × L → ℚ)) (color : R → G)
    (colors : Finset G) (h : G) (q : ℕ)
    (ht : ∀ k v, B k v = -1 ∨ B k v = 0 ∨ B k v = 1)
    (k : ColorRows q color (translated colors h)) (v : Word (fun _ : Fin q => L)) :
    encoder B color colors h q k v = -1 ∨ encoder B color colors h q k v = 0 ∨
      encoder B color colors h q k v = 1 := by
  unfold encoder tensorRows
  apply Finset.prod_induction _ (fun x : ℚ => x = -1 ∨ x = 0 ∨ x = 1)
  · intro a b ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> norm_num [ha,hb]
  · exact Or.inr (Or.inr rfl)
  · intro i _
    exact ht _ _

/-- Lemma 3: any sufficient translates of a finite colored basis recover, and
the rank equals the full convolution mass of the transmitted translate. -/
theorem selection_by_total_color (B : Module.Basis R F (L × L → F)) (color : R → G)
    (colors : Finset G) (h : G) (q : ℕ) (a : Fin q → F)
    (hs : SufficientTranslates B color colors) :
    (∃ P, FeasibleZero a (encoder B color colors h q) P) ∧
      (encoder B color colors h q).rank =
        ∑ g ∈ Finset.univ.filter (translated colors h), convolutionPower (colorMass color) q g :=
  ⟨(feasibleZero_exists_iff _ _).mpr (encoder_recovers B color colors h q hs),
    (encoder_rank_card B color colors h q).trans (selected_card color colors h q)⟩


/-- The rational version of Lemma 3 with all three conclusions in one statement. -/
theorem selection_by_total_color_ternary (B : Module.Basis R ℚ (L × L → ℚ)) (color : R → G)
    (colors : Finset G) (h : G) (q : ℕ) (a : Fin q → ℚ)
    (hs : SufficientTranslates B color colors)
    (ht : ∀ k v, B k v = -1 ∨ B k v = 0 ∨ B k v = 1) :
    (∃ P, FeasibleZero a (encoder B color colors h q) P) ∧
      (encoder B color colors h q).rank =
        ∑ g ∈ Finset.univ.filter (translated colors h), convolutionPower (colorMass color) q g ∧
      ∀ k v, encoder B color colors h q k v = -1 ∨ encoder B color colors h q k v = 0 ∨
        encoder B color colors h q k v = 1 := by
  obtain ⟨hp, hr⟩ := selection_by_total_color B color colors h q a hs
  exact ⟨hp, hr, encoder_ternary B color colors h q ht⟩

end
end Reconstruction.ReleaseColor
