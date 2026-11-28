import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
Finite random-endpoint lemmas for P11. A designated ordered cell is eligible
for exactly one mask. Given eligibility, E is the set of endpoint positions.
The two physical ports are drawn from one cell without replacement.
-/

namespace RandomEndpoint

open scoped BigOperators

abbrev DistinctPair (T : Type*) := {p : T × T // p.1 ≠ p.2}

theorem card_distinctPair (T : Type*) [Fintype T] :
    Nat.card (DistinctPair T) = Fintype.card T * (Fintype.card T - 1) := by
  classical
  let e : {p : T × T // p.1 = p.2} ≃ T :=
    { toFun := fun p => p.val.1
      invFun := fun a => ⟨(a,a), rfl⟩
      left_inv := by
        rintro ⟨⟨a,b⟩, h⟩
        change a = b at h
        subst b
        rfl
      right_inv := fun _ => rfl }
  change Nat.card {p : T × T // ¬ (p.1 = p.2)} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun p : T × T => p.1 = p.2),
    Fintype.card_congr e, Fintype.card_prod, Nat.mul_sub, Nat.mul_one]

/-- Actual success event in the uniform finite mask-and-draw sample space. -/
abbrev SuccessPair {s H : ℕ} (eligible : Fin s) (E : Finset (Fin H)) :=
  {p : Fin s × DistinctPair (Fin H) //
    p.1 = eligible ∧ p.2.val.1 ∈ E ∧ p.2.val.2 ∈ E}

def successPairEquiv {s H : ℕ} (eligible : Fin s) (E : Finset (Fin H)) :
    SuccessPair eligible E ≃ DistinctPair (↥E) where
  toFun p :=
    ⟨(⟨p.val.2.val.1, p.prop.2.1⟩, ⟨p.val.2.val.2, p.prop.2.2⟩),
      fun eq => p.val.2.prop (congrArg Subtype.val eq)⟩
  invFun p :=
    ⟨(eligible, ⟨(p.val.1.val, p.val.2.val),
      fun eq => p.prop (Subtype.ext eq)⟩), ⟨rfl,p.val.1.prop,p.val.2.prop⟩⟩
  left_inv := by
    rintro ⟨⟨μ,⟨⟨a,b⟩,hne⟩⟩, hμ, ha, hb⟩
    change μ = eligible at hμ
    subst μ
    rfl
  right_inv := by
    rintro ⟨⟨⟨a,ha⟩,⟨b,hb⟩⟩,hne⟩
    rfl

theorem card_successPair {s H : ℕ} (eligible : Fin s) (E : Finset (Fin H)) :
    Nat.card (SuccessPair eligible E) = E.card * (E.card - 1) := by
  rw [Nat.card_congr (successPairEquiv eligible E), card_distinctPair]
  simp

noncomputable def probPair {s H : ℕ} (eligible : Fin s) (E : Finset (Fin H)) : ℚ :=
  (Nat.card (SuccessPair eligible E) : ℚ) / (Nat.card (Fin s × DistinctPair (Fin H)) : ℚ)

/-- Probability as in the same-cell branch of the calculation, not the
independent-ports approximation. Nat subtractions also cover an empty E. -/
theorem pair_exact {s H : ℕ} (eligible : Fin s) (E : Finset (Fin H)) :
    probPair eligible E =
    (E.card * (E.card - 1) : ℕ) / (s * (H * (H - 1)) : ℕ) := by
  unfold probPair
  rw [card_successPair, Nat.card_prod, Nat.card_fin, card_distinctPair]
  simp

/-- Single-port version: the finite success set consists of one mask for
each acceptable endpoint slot. -/
abbrev SuccessSingle {s H : ℕ} (eligible : Fin s) (E : Finset (Fin H)) :=
  {p : Fin s × Fin H // p.1 = eligible ∧ p.2 ∈ E}

def successSingleEquiv {s H : ℕ} (eligible : Fin s) (E : Finset (Fin H)) :
    SuccessSingle eligible E ≃ ↥E where
  toFun p := ⟨p.val.2,p.prop.2⟩
  invFun p := ⟨(eligible,p.val),rfl,p.prop⟩
  left_inv := by
    rintro ⟨⟨a,b⟩,heq,hb⟩
    change a = eligible at heq
    subst a
    rfl
  right_inv := by rintro ⟨a,ha⟩; rfl

theorem single_exact {s H : ℕ} (eligible : Fin s) (E : Finset (Fin H)) :
    (Nat.card (SuccessSingle eligible E) : ℚ) / (Nat.card (Fin s × Fin H) : ℚ) =
      (E.card : ℚ) / (s * H : ℕ) := by
  rw [Nat.card_congr (successSingleEquiv eligible E), Nat.card_prod, Nat.card_fin, Nat.card_fin]
  simp

theorem single_native {b s L : ℕ} (eligible : Fin s) (E : Finset (Fin (b*L)))
    (hb : 0<b) (hL : 0<L) (hE : E.card = b*s) :
    (Nat.card (SuccessSingle eligible E) : ℚ) / (Nat.card (Fin s × Fin (b*L)) : ℚ) = 1/(L:ℚ) := by
  have hs : 0 < s := Fin.pos_iff_nonempty.mpr ⟨eligible⟩
  have hb' : (0:ℚ) < b := by exact_mod_cast hb
  have hL' : (0:ℚ) < L := by exact_mod_cast hL
  have hs' : (0:ℚ) < s := by exact_mod_cast hs
  rw [single_exact, hE]
  push_cast
  field_simp

/-- H=bL, E.card=bs, s masks. For two ports of one cell the success
probability is at least (1−1/b)/L². Only H≥2 is needed for the sample space
to be nonempty. -/
theorem sameType_lower {b s L : ℕ} (eligible : Fin s) (E : Finset (Fin (b*L)))
    (hb : 0<b) (hL : 0<L) (hH : 1<b*L) (hE : E.card = b*s) :
    (1-1/(b:ℚ))/(L:ℚ)^2 ≤ probPair eligible E := by
  have hs : 0<s := Fin.pos_iff_nonempty.mpr ⟨eligible⟩
  have hb' : (0:ℚ) < b := by exact_mod_cast hb
  have hL' : (0:ℚ) < L := by exact_mod_cast hL
  have hs' : (0:ℚ) < s := by exact_mod_cast hs
  have hs1 : (1:ℚ) ≤ s := by exact_mod_cast hs
  have hb1 : (1:ℚ) ≤ b := by exact_mod_cast hb
  have hH' : (1:ℚ) < (b:ℚ)*L := by exact_mod_cast hH
  have hrem : 0 < (b:ℚ)*L - 1 := sub_pos.mpr hH'
  have hm : 1 ≤ b*s := Nat.succ_le_of_lt (Nat.mul_pos hb hs)
  have hp : 1 ≤ b*L := Nat.le_of_lt hH
  rw [pair_exact, hE]
  push_cast [Nat.cast_sub hm, Nat.cast_sub hp]
  calc
    _ = ((b:ℚ)-1)/(b*(L:ℚ)^2) := by field_simp
    _ ≤ ((b:ℚ)*s-1)/(b*(L:ℚ)^2) := by
      apply (div_le_div_iff_of_pos_right (by positivity)).mpr
      nlinarith
    _ ≤ ((b:ℚ)*s-1)/(L*((b:ℚ)*L-1)) :=
      div_le_div_of_nonneg_left (by nlinarith) (by positivity) (by nlinarith)
    _ = _ := by field_simp

/-- Independent cells use the product of their two actual finite sample
spaces, and then the two successes have probability exactly 1/L². -/
theorem distinctTypes_exact {b s s' L : ℕ} (e₁ : Fin s) (e₂ : Fin s')
    (E₁ E₂ : Finset (Fin (b*L))) (hb : 0<b) (hL : 0<L)
    (hE₁ : E₁.card=b*s) (hE₂ : E₂.card=b*s') :
    (Nat.card (SuccessSingle e₁ E₁ × SuccessSingle e₂ E₂) : ℚ) /
      (Nat.card ((Fin s × Fin (b*L)) × (Fin s' × Fin (b*L))) : ℚ) = 1/(L:ℚ)^2 := by
  let Y₁ := Fin s × Fin (b*L)
  let Y₂ := Fin s' × Fin (b*L)
  have h₁ := single_native e₁ E₁ hb hL hE₁
  have h₂ := single_native e₂ E₂ hb hL hE₂
  change (Nat.card (SuccessSingle e₁ E₁ × SuccessSingle e₂ E₂) : ℚ) /
      (Nat.card (Y₁ × Y₂) : ℚ) = _
  rw [Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul, ← div_mul_div_comm]
  change (Nat.card (SuccessSingle e₁ E₁) : ℚ) / (Nat.card Y₁ : ℚ) *
    ((Nat.card (SuccessSingle e₂ E₂) : ℚ) / (Nat.card Y₂ : ℚ)) = _
  rw [h₁,h₂]
  ring

/-- Pure scaling of the crude moment bound 4HP into the relative form used
in Chebyshev. H padded cell load, P packets; PL=HD and PL≤2M. -/
theorem relative_variance_bound (H P L M D : ℚ) (hP : 0≤P) (hL : 0<L) (hD : 0<D)
    (hpack : P*L=H*D) (hbound : P*L ≤ 2*M) :
    4*H*P ≤ (64*L^3/D)*(M/(2*L^2))^2 := by
  have hmul : H*P = (P*L)^2/(D*L) := by
    apply (eq_div_iff (by positivity)).2
    calc
      H*P*(D*L) = (H*D)*(P*L) := by ring
      _ = (P*L)^2 := by rw [← hpack]; ring
  have hs := pow_le_pow_left₀ (mul_nonneg hP hL.le) hbound 2
  calc
    4*H*P = 4*((P*L)^2/(D*L)) := by rw [mul_assoc, hmul]
    _ ≤ 4*((2*M)^2/(D*L)) := by
      exact mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right (by positivity)).2 hs) (by norm_num)
    _ = _ := by
      field_simp
      ring

section Concentration

variable {Ω : Type*} [Fintype Ω]

noncomputable def probability (w : Ω → ℚ) (E : Ω → Prop) [DecidablePred E] : ℚ :=
  ∑ ω, if E ω then w ω else 0

noncomputable def quadraticMoment (w X : Ω → ℚ) (μ : ℚ) : ℚ :=
  ∑ ω, w ω * (X ω - μ)^2

/-- Linearity for the actual finite count of successful columns; the
events for different disjoint equality vertices need not be independent. -/
theorem expectation_count {I : Type*} [Fintype I] (w : Ω → ℚ)
    (E : I → Ω → Prop) [∀ i, DecidablePred (E i)] (c : ℚ)
    (h : ∀ i, c ≤ probability w (E i)) :
    (Fintype.card I : ℚ) * c ≤ ∑ ω, w ω * ∑ i, if E i ω then (1:ℚ) else 0 := by
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  have h' : (∑ _ : I, c) ≤ (∑ i, probability w (E i)) :=
    Finset.sum_le_sum fun i _ => h i
  simpa [probability] using h'

/-- Finite one-sided Chebyshev from the exact squared deviation. The center
is arbitrary; instantiating it to the mean makes the moment the variance. -/
theorem lowerTail (w X : Ω → ℚ) (μ e : ℚ) (he : 0 < e) (hw : ∀ ω, 0 ≤ w ω) :
    probability w (fun ω => X ω < μ-e) ≤ quadraticMoment w X μ / e^2 := by
  refine (le_div_iff₀ (by positivity)).2 ?_
  rw [probability, quadraticMoment, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : X ω < μ-e
  · rw [if_pos h]
    apply mul_le_mul_of_nonneg_left _ (hw ω)
    have hq : e ≤ μ-X ω := by linarith
    have hs := pow_le_pow_left₀ he.le hq 2
    nlinarith
  · rw [if_neg h, zero_mul]
    exact mul_nonneg (hw ω) (sq_nonneg _)

theorem probability_mono (w : Ω → ℚ) (E G : Ω → Prop) [DecidablePred E] [DecidablePred G]
    (hw : ∀ ω, 0 ≤ w ω) (h : ∀ ω, E ω → G ω) :
    probability w E ≤ probability w G := by
  unfold probability
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω
  · rw [if_pos he, if_pos (h ω he)]
  · rw [if_neg he]
    split_ifs <;> first | exact hw ω | exact le_rfl

/-- One common success event for both endpoints. Changing the center to
the mean of each endpoint count gives the usual variance/epsilon² bound.
No independence assumption is needed for this final union step. -/
theorem bothGood (w X Y : Ω → ℚ) (μ ν T e : ℚ) (he : 0<e)
    (hw : ∀ ω, 0 ≤ w ω) (hnorm : (∑ ω, w ω) = 1)
    (hX : T ≤ μ-e) (hY : T ≤ ν-e) :
    1-(quadraticMoment w X μ + quadraticMoment w Y ν)/e^2 ≤
      probability w (fun ω => T ≤ X ω ∧ T ≤ Y ω) := by
  have hl := (probability_mono w _ _ hw (fun ω (h : X ω < T) => h.trans_le hX)).trans
    (lowerTail w X μ e he hw)
  have hr := (probability_mono w _ _ hw (fun ω (h : Y ω < T) => h.trans_le hY)).trans
    (lowerTail w Y ν e he hw)
  have hcover : 1 ≤ probability w (fun ω => T ≤ X ω ∧ T ≤ Y ω) +
      probability w (fun ω => X ω < T) + probability w (fun ω => Y ω < T) := by
    rw [← hnorm, probability, probability, probability, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    by_cases hx : X ω < T <;> by_cases hy : Y ω < T
    all_goals simp only [← not_lt, hx, hy]
    all_goals simp
    all_goals linarith [hw ω]
  rw [add_div]
  linarith

/-- Plug in the paper's relative slack and variance target. The actual
random-layout model must still establish the two moment bounds and the
expectation lower bounds. Here L is a positive rational grid size and D the
ordered-cell count; D=L^12 gives an explicit O(L^-5) failure bound. -/
theorem native_tail_from_moments (w X Y : Ω → ℚ) (μ ν A L D b : ℚ)
    (hA : 0<A) (hL : 0<L) (hD : 0<D) (hw : ∀ ω, 0≤w ω) (hnorm : (∑ ω, w ω) = 1)
    (hμ : (1-1/b)*A ≤ μ) (hν : (1-1/b)*A ≤ ν)
    (hvarX : quadraticMoment w X μ ≤ 64*L^3/D*A^2)
    (hvarY : quadraticMoment w Y ν ≤ 64*L^3/D*A^2) :
    1-128*L^7/D ≤ probability w (fun ω =>
      (1-1/b-1/L^2)*A ≤ X ω ∧ (1-1/b-1/L^2)*A ≤ Y ω) := by
  let e := A / L^2
  have he : 0<e := by dsimp [e]; positivity
  have hT : (1-1/b-1/L^2)*A = (1-1/b)*A - e := by
    dsimp [e]
    field_simp
  have hg := bothGood w X Y μ ν ((1-1/b-1/L^2)*A) e he hw hnorm
    (by rw [hT]; linarith) (by rw [hT]; linarith)
  refine le_trans ?_ hg
  suffices hz : (quadraticMoment w X μ + quadraticMoment w Y ν)/e^2 ≤ 128*L^7/D by linarith
  calc
    _ ≤ (2*(64*L^3/D*A^2))/e^2 :=
      (div_le_div_iff_of_pos_right (by positivity)).2 (by linarith)
    _ = _ := by
      dsimp [e]
      field_simp
      ring

end Concentration

#print axioms card_distinctPair
#print axioms card_successPair
#print axioms pair_exact
#print axioms single_exact
#print axioms single_native
#print axioms sameType_lower
#print axioms distinctTypes_exact
#print axioms relative_variance_bound
#print axioms expectation_count
#print axioms lowerTail
#print axioms probability_mono
#print axioms bothGood
#print axioms native_tail_from_moments

end RandomEndpoint