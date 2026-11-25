import AffineEdgeDimension
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Abel

open scoped BigOperators Polynomial

namespace AffineEdge

noncomputable section

variable {q : ℕ} {F H : Type*} [Field F] [AddCommGroup H] [Module F H]
variable {slope : Fin q → F} {col : Bits q → Kind q → H}

/-- A neighbor column in the center span must be a nuisance, and it belongs
to the smaller span of the one-match center columns. -/
theorem CenterCondition.neighbor_mem_near (hc : CenterCondition slope col)
    (a : Bits q) (t : Fin q) (k : Kind q)
    (hz : col (flip t a) k ∈ centerSpan (F := F) col a) :
    k ≠ some t ∧ col (flip t a) k ∈ nearSpan (F := F) col a := by
  classical
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hz
  let e : (Kind q × Bool) ⊕ Unit → Slot q :=
    Sum.elim Sum.inl (fun _ => .inr (t, k))
  have he : Function.Injective e := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (Sum.inl.inj h)
    · cases h
    · cases h
    · exact congrArg Sum.inr (Subsingleton.elim i j)
  let x : (Kind q × Bool) ⊕ Unit → F :=
    Sum.elim (fun p => if p.2 then slope t * f p.1 else f p.1) (fun _ => -1)
  have hs : (∑ j, x j • slotColumn slope col a (e j)) = 0 := by
    simp only [Fintype.sum_sum_type, e, Sum.elim_inl, Sum.elim_inr, slotColumn_center,
      slotColumn_neighbor, sum_centerVector, x, Bool.false_eq_true, if_false, if_true,
      Fintype.sum_unique, neg_smul, one_smul]
    simp_rw [mul_smul, ← Finset.smul_sum, hf]
    simp [affineVector]
  constructor
  · intro hk
    have h := hc.restrict a e he x hs (.inr ()) (some t) (by simp [e, hk, targetSlot])
    exact neg_ne_zero.mpr one_ne_zero h
  · have h0 : f none = 0 := hc.restrict a e he x hs (.inl (none, false)) none rfl
    rw [Fintype.sum_option, h0, zero_smul, zero_add] at hf
    rw [← hf]
    exact Submodule.sum_mem _ fun t _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

/-- An endpoint is exceptional if some nuisance column across its edge lies
outside the span of its one-match columns. -/
def Exceptional (col : Bits q → Kind q → H) (a : Bits q) (t : Fin q) : Prop :=
  ∃ k : Kind q, k ≠ some t ∧ col (flip t a) k ∉ nearSpan (F := F) col a

private theorem near_le_adjacent_center [Module.Finite F H]
    (hc : CenterCondition slope col) (a : Bits q) (t : Fin q)
    (h : ¬ Exceptional (F := F) col a t) :
    nearSpan (F := F) col a ≤ centerSpan col (flip t a) := by
  classical
  let s : {k : Kind q // k ≠ some t} → H := fun k => col (flip t a) k.val
  let U := Submodule.span F (Set.range s)
  have hU : U ≤ nearSpan (F := F) col a := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    by_contra hn
    exact h ⟨k.val, k.property, hn⟩
  have hN : Module.finrank F (nearSpan (F := F) col a) = q := by
    have hi : Function.Injective (some : Fin q → Kind q) := fun _ _ e => Option.some.inj e
    simpa [nearSpan] using finrank_span_eq_card ((hc.independent a).comp some hi)
  have hUq : Module.finrank F U = q := by
    have hi : LinearIndependent F s :=
      (hc.independent (flip t a)).comp Subtype.val Subtype.val_injective
    change Module.finrank F (Submodule.span F (Set.range s)) = q
    rw [finrank_span_eq_card hi]
    letI : Unique {k : Kind q // k = some t} :=
      ⟨⟨some t, rfl⟩, fun z => Subtype.ext z.property⟩
    have hone : Fintype.card {k : Kind q // k = some t} = 1 := Fintype.card_unique
    rw [Fintype.card_subtype_compl (fun k : Kind q => k = some t),
      hone, Fintype.card_option, Fintype.card_fin]
    omega
  rw [← Submodule.eq_of_le_of_finrank_le hU (by rw [hN, hUq])]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact col_mem_centerSpan (flip t a) k.val

theorem CenterCondition.exceptional_edge [Module.Finite F H] (hc : CenterCondition slope col)
    (a : Bits q) (t : Fin q) :
    Exceptional (F := F) col a t ∨ Exceptional (F := F) col (flip t a) t := by
  classical
  by_contra! h
  have hN := near_le_adjacent_center hc (flip t a) t h.2
  rw [flip_flip] at hN
  have hv : col (flip t a) none ∈ nearSpan (F := F) col a := by
    by_contra hn
    exact h.1 ⟨none, by simp, hn⟩
  have hW : centerSpan (F := F) col (flip t a) ≤ centerSpan col a := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    cases k with
    | none => exact nearSpan_le_centerSpan a hv
    | some s => exact hN (Submodule.subset_span ⟨s, rfl⟩)
  exact (hc.neighbor_mem_near a t (some t) (hW (col_mem_centerSpan _ _))).1 rfl

private theorem affine_pair_independent {V : Type*} [AddCommGroup V] [Module F V]
    {s t : F} {u v : V} (hs : s ≠ t) (hu : u ≠ 0) (hv : v ≠ 0) :
    LinearIndependent F (fun b : Bool => if b then affineVector t v else affineVector s u) := by
  rw [Fintype.linearIndependent_iff]
  intro x hx b
  rw [Fintype.sum_bool] at hx
  simp only [if_true, Bool.false_eq_true, if_false] at hx
  have h1 : x true • v + x false • u = 0 := congrArg Prod.fst hx
  have h2 : t • (x true • v) + s • (x false • u) = 0 := by
    have h := congrArg Prod.snd hx
    simpa only [Prod.snd_add, Prod.smul_snd, Prod.snd_zero, affineVector, smul_comm (x true) t,
      smul_comm (x false) s] using h
  have h3 : s • (x true • v) + s • (x false • u) = 0 := by
    simpa only [smul_add, smul_zero] using congrArg (fun z : V => s • z) h1
  have h4 : (t - s) • (x true • v) = 0 := by
    rw [sub_smul]
    calc
      _ = (t • (x true • v) + s • (x false • u)) -
          (s • (x true • v) + s • (x false • u)) := by abel
      _ = 0 := by rw [h2, h3, sub_zero]
  have ht : x true = 0 :=
    (smul_eq_zero.mp ((smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hs.symm))).resolve_right hv
  cases b
  · apply (smul_eq_zero.mp _).resolve_right hu
    simpa only [ht, zero_smul, zero_add] using h1
  · exact ht

theorem CenterCondition.dimension_exceptional [Module.Finite F H] (hc : CenterCondition slope col)
    (a : Bits q) (t : Fin q) (h : Exceptional (F := F) col a t) :
    3*q+3 ≤ 2 * Module.finrank F H := by
  obtain ⟨k, hk, hz⟩ := h
  let p : Unit → Fin q × Kind q := fun _ => (t, k)
  have hn : (centerSpan (F := F) col a).mkQ (col (flip t a) k) ≠ 0 := by
    intro hmem
    exact hz (hc.neighbor_mem_near a t k ((Submodule.Quotient.mk_eq_zero _).mp hmem)).2
  have hi : LinearIndependent F (fun j =>
      centerQuotient (F := F) col a (slotColumn slope col a (.inr (p j)))) := by
    apply linearIndependent_unique
    intro he
    apply hn
    simpa only [p, slotColumn_neighbor, centerQuotient_affineVector] using
      congrArg Prod.fst he
  simpa using hc.dimension_extra a p (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hk) hi

theorem CenterCondition.dimension_two_exceptional [Module.Finite F H]
    (hc : CenterCondition slope col) (hslope : Function.Injective slope)
    (a : Bits q) {s t : Fin q} (hst : s ≠ t)
    (hs : Exceptional (F := F) col a s) (ht : Exceptional (F := F) col a t) :
    3*q+4 ≤ 2 * Module.finrank F H := by
  obtain ⟨k, hk, hz⟩ := hs
  obtain ⟨l, hl, hw⟩ := ht
  let p (b : Bool) : Fin q × Kind q := if b then (t, l) else (s, k)
  have hp : Function.Injective p := by
    intro i j h
    cases i <;> cases j <;> simp_all [p]
  have hn (b : Bool) : (p b).2 ≠ some (p b).1 := by
    cases b <;> simpa [p]
  let W := centerSpan (F := F) col a
  have hu : W.mkQ (col (flip s a) k) ≠ 0 := by
    intro h
    exact hz (hc.neighbor_mem_near a s k ((Submodule.Quotient.mk_eq_zero W).mp h)).2
  have hv : W.mkQ (col (flip t a) l) ≠ 0 := by
    intro h
    exact hw (hc.neighbor_mem_near a t l ((Submodule.Quotient.mk_eq_zero W).mp h)).2
  have hi : LinearIndependent F (fun j =>
      centerQuotient (F := F) col a (slotColumn slope col a (.inr (p j)))) := by
    convert affine_pair_independent (fun he => hst (hslope he)) hu hv using 1
    funext b
    cases b <;> simp [p, W]
  have h := hc.dimension_extra a p hp hn hi
  simp only [Fintype.card_bool] at h
  omega

/-- Sharp affine obstruction: the middle measurement dimension is too
small to support the exceptional endpoints required by the cube. -/
theorem rank_lower_of_centerCondition [Module.Finite F H]
    (hq : 2 ≤ q) (hc : CenterCondition slope col) (hslope : Function.Injective slope) :
    q + (q+1)/2 + 2 ≤ Module.finrank F H := by
  classical
  by_contra! hlow
  have hv (a : Bits q) : (Finset.univ.filter (Exceptional (F := F) col a)).card ≤ q % 2 := by
    by_cases he : q % 2 = 0
    · rw [he, Nat.le_zero, Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hb := hc.dimension_exceptional a t (Finset.mem_filter.mp ht).2
      omega
    · have he' : q % 2 = 1 := by omega
      rw [he', Finset.card_le_one]
      intro s hs t ht
      by_contra hst
      have hb := hc.dimension_two_exceptional hslope a hst (Finset.mem_filter.mp hs).2
        (Finset.mem_filter.mp ht).2
      omega
  have hcount := edge_count (Exceptional (F := F) col) (hc.exceptional_edge) hv
  omega

/-- The rank lower bound for the paper's actual physical matrix, for arbitrary
field-valued common measurements and distinct nonzero evaluation sites. -/
theorem paired_rank_lower {ι : Type*} [Fintype ι] {sites : Fin q → F}
    {C : Matrix ι (Word q) F} {P : Word q → Word q → F[X]}
    (hq : 2 ≤ q) (hinj : Function.Injective sites) (hn : ∀ t, sites t ≠ 0)
    (hp : PairedCondition sites C (q-2) P) :
    q + (q+1)/2 + 2 ≤ C.rank := by
  classical
  let V := Submodule.span F (Set.range C.col)
  let c (a : Bits q) (k : Kind q) : V :=
    ⟨C.col (hardWord a k), Submodule.subset_span ⟨_, rfl⟩⟩
  have hc0 := centerCondition_of_paired hq hinj hn hp
  have hc : CenterCondition (fun t => -(sites t)⁻¹) c := by
    intro a x hx k
    apply hc0 a x _ k
    have he := congrArg (V.subtype.prodMap V.subtype) hx
    simpa only [map_sum, map_smul, map_zero, LinearMap.prodMap_apply, slotColumn,
      Submodule.subtype_apply, Submodule.coe_smul_of_tower, c, Matrix.col] using he
  rw [Matrix.rank_eq_finrank_span_cols]
  exact rank_lower_of_centerCondition hq hc
    (fun i j h => hinj (inv_injective (neg_injective h)))

end

end AffineEdge
