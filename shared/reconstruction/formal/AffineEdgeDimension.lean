import AffineEdgeCenter
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic

open scoped BigOperators

namespace AffineEdge

noncomputable section

variable {q : ℕ} {F H : Type*} [Field F] [AddCommGroup H] [Module F H]
variable {slope : Fin q → F} {col : Bits q → Kind q → H}

def centerVector (col : Bits q → Kind q → H) (a : Bits q) (p : Kind q × Bool) : H × H :=
  if p.2 then (0, col a p.1) else (col a p.1, 0)

def affineVector (s : F) (z : H) : H × H := (z, s • z)

@[simp] theorem slotColumn_center (a : Bits q) (p : Kind q × Bool) :
    slotColumn slope col a (.inl p) = centerVector col a p := by
  rcases p with ⟨k, b⟩
  cases b <;> simp [slotColumn, centerVector, placement, intercept, gradient, step]

@[simp] theorem slotColumn_neighbor (a : Bits q) (t : Fin q) (k : Kind q) :
    slotColumn slope col a (.inr (t, k)) = affineVector (slope t) (col (flip t a) k) := by
  simp [slotColumn, affineVector, placement, intercept, gradient, step]

theorem sum_centerVector (a : Bits q) (x : Kind q × Bool → F) :
    (∑ p, x p • centerVector col a p) =
      (∑ k : Kind q, x (k, false) • col a k, ∑ k : Kind q, x (k, true) • col a k) := by
  apply Prod.ext
  · simp [Prod.fst_sum, Fintype.sum_prod_type, centerVector]
  · simp [Prod.snd_sum, Fintype.sum_prod_type, centerVector]

private def extendCoeff {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (e : ι → κ) (x : ι → F) (j : κ) : F :=
  ∑ i, if e i = j then x i else 0

private theorem extendCoeff_apply {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    {e : ι → κ} (he : Function.Injective e) (x : ι → F) (i : ι) :
    extendCoeff e x (e i) = x i := by
  unfold extendCoeff
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    exact if_neg (fun h => hj (he h))
  · simp

private theorem sum_extendCoeff {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup V] [Module F V] (e : ι → κ) (x : ι → F) (v : κ → V) :
    (∑ j, extendCoeff e x j • v j) = ∑ i, x i • v (e i) := by
  simp only [extendCoeff, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp [ite_smul]

/-- Restrict the affine test to any indexed family of selected columns. -/
theorem CenterCondition.restrict (hc : CenterCondition slope col) (a : Bits q)
    {ι : Type*} [Fintype ι] (e : ι → Slot q) (he : Function.Injective e)
    (x : ι → F) (hx : (∑ i, x i • slotColumn slope col a (e i)) = 0)
    (i : ι) (k : Kind q) (hi : e i = targetSlot k) : x i = 0 := by
  classical
  have hz := hc a (extendCoeff e x) ((sum_extendCoeff e x _).trans hx) k
  rw [← hi, extendCoeff_apply he] at hz
  exact hz

theorem CenterCondition.independent (hc : CenterCondition slope col) (a : Bits q) :
    LinearIndependent F (col a) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro x hx k
  cases k with
  | none =>
    let e (j : Kind q) : Slot q := .inl (j, false)
    have he : Function.Injective e := fun _ _ h => (Prod.mk.inj (Sum.inl.inj h)).1
    have hz : (∑ j, x j • slotColumn slope col a (e j)) = 0 := by
      apply Prod.ext
      · simpa [e, centerVector, Prod.fst_sum] using hx
      · simp [e, centerVector, Prod.snd_sum]
    exact hc.restrict a e he x hz none none rfl
  | some t =>
    let e (j : Kind q) : Slot q := .inr (t, j)
    have he : Function.Injective e := fun _ _ h => (Prod.mk.inj (Sum.inr.inj h)).2
    have hz : (∑ j, x j • slotColumn slope col (flip t a) (e j)) = 0 := by
      apply Prod.ext
      · simpa [e, affineVector, Prod.fst_sum] using hx
      · simp only [e, slotColumn_neighbor, affineVector, flip_flip, Prod.snd_sum,
          Prod.smul_snd, Prod.snd_zero]
        simp_rw [smul_comm (x _) (slope t), ← Finset.smul_sum, hx, smul_zero]
    exact hc.restrict (flip t a) e he x hz (some t) (some t) rfl

def centerSpan (col : Bits q → Kind q → H) (a : Bits q) : Submodule F H :=
  Submodule.span F (Set.range (col a))

def nearSpan (col : Bits q → Kind q → H) (a : Bits q) : Submodule F H :=
  Submodule.span F (Set.range (fun t : Fin q => col a (some t)))

theorem col_mem_centerSpan (a : Bits q) (k : Kind q) :
    col a k ∈ centerSpan (F := F) col a :=
  Submodule.subset_span ⟨k, rfl⟩

theorem nearSpan_le_centerSpan (a : Bits q) :
    nearSpan (F := F) col a ≤ centerSpan col a := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  exact col_mem_centerSpan a (some t)

private def extraEmbedding {ι : Type*} (p : ι → Fin q × Kind q) :
    ((Kind q × Bool) ⊕ (Fin q ⊕ ι)) → Slot q
  | .inl j => .inl j
  | .inr (.inl t) => .inr (t, some t)
  | .inr (.inr j) => .inr (p j)

private theorem extraEmbedding_injective {ι : Type*} {p : ι → Fin q × Kind q}
    (hp : Function.Injective p) (hn : ∀ j, (p j).2 ≠ some (p j).1) :
    Function.Injective (extraEmbedding p) := by
  rintro (i | t | j) (i' | t' | j') h <;> simp only [extraEmbedding, Sum.inl.injEq,
    Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at h ⊢
  · exact h
  · exact congrArg Prod.fst h
  · exact (hn j' (by rw [← h])).elim
  · exact (hn j (by rw [h])).elim
  · exact hp h

def centerQuotient (col : Bits q → Kind q → H) (a : Bits q) :
    H × H →ₗ[F] (H ⧸ centerSpan (F := F) col a) × (H ⧸ centerSpan (F := F) col a) :=
  ((centerSpan (F := F) col a).mkQ.comp (LinearMap.fst F H H)).prod
    ((centerSpan (F := F) col a).mkQ.comp (LinearMap.snd F H H))

@[simp] theorem centerQuotient_affineVector (a : Bits q) (s : F) (z : H) :
    centerQuotient col a (affineVector s z) =
      affineVector s ((centerSpan (F := F) col a).mkQ z) := by
  simp [centerQuotient, affineVector]

@[simp] theorem centerQuotient_centerVector (a : Bits q) (p : Kind q × Bool) :
    centerQuotient (F := F) col a (centerVector col a p) = 0 := by
  have hz : (centerSpan (F := F) col a).mkQ (col a p.1) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (col_mem_centerSpan a p.1)
  rcases p with ⟨k, b⟩
  cases b <;> simp [centerQuotient, centerVector, hz]

/-- Center columns and the neighbor targets, together with any further
nuisance columns whose images are independent after removing the center. -/
theorem CenterCondition.independent_extra (hc : CenterCondition slope col)
    (a : Bits q) {ι : Type*} [Fintype ι] (p : ι → Fin q × Kind q)
    (hp : Function.Injective p) (hn : ∀ j, (p j).2 ≠ some (p j).1)
    (hi : LinearIndependent F (fun j =>
      centerQuotient (F := F) col a (slotColumn slope col a (.inr (p j))))) :
    LinearIndependent F (fun i => slotColumn slope col a (extraEmbedding p i)) := by
  classical
  rw [Fintype.linearIndependent_iff] at hi ⊢
  intro x hx i
  have ht (t : Fin q) : x (.inr (.inl t)) = 0 :=
    hc.restrict a _ (extraEmbedding_injective hp hn) x hx _ (some t) rfl
  have hsplit : (∑ j : Kind q × Bool, x (.inl j) • centerVector col a j) +
      (∑ j : ι, x (.inr (.inr j)) • slotColumn slope col a (.inr (p j))) = 0 := by
    simpa only [Fintype.sum_sum_type, extraEmbedding, slotColumn_center, ht, zero_smul,
      Finset.sum_const_zero, zero_add] using hx
  have he := congrArg (centerQuotient (F := F) col a) hsplit
  have hz (j : ι) : x (.inr (.inr j)) = 0 := hi _ (by
    simpa only [map_add, map_sum, map_smul, centerQuotient_centerVector, smul_zero,
      Finset.sum_const_zero, zero_add, map_zero] using he) j
  have hcSum : (∑ j : Kind q × Bool, x (.inl j) • centerVector col a j) = 0 := by
    simpa only [hz, zero_smul, Finset.sum_const_zero, add_zero] using hsplit
  have hc0 : (∑ j : Kind q, x (.inl (j, false)) • col a j) = 0 := by
    have h := congrArg Prod.fst hcSum
    rw [sum_centerVector] at h
    exact h
  have hc1 : (∑ j : Kind q, x (.inl (j, true)) • col a j) = 0 := by
    have h := congrArg Prod.snd hcSum
    rw [sum_centerVector] at h
    exact h
  rcases i with ⟨j, b⟩ | t | j
  · cases b
    · exact (Fintype.linearIndependent_iff.mp (hc.independent a)) _ hc0 j
    · exact (Fintype.linearIndependent_iff.mp (hc.independent a)) _ hc1 j
  · exact ht t
  · exact hz j

theorem CenterCondition.dimension_extra [Module.Finite F H]
    (hc : CenterCondition slope col) (a : Bits q) {ι : Type*} [Fintype ι]
    (p : ι → Fin q × Kind q) (hp : Function.Injective p)
    (hn : ∀ j, (p j).2 ≠ some (p j).1)
    (hi : LinearIndependent F (fun j =>
      centerQuotient (F := F) col a (slotColumn slope col a (.inr (p j))))) :
    3*q+2 + Fintype.card ι ≤ 2 * Module.finrank F H := by
  have h := (hc.independent_extra a p hp hn hi).fintype_card_le_finrank
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
    Fintype.card_bool, Module.finrank_prod] at h
  omega

end

end AffineEdge
