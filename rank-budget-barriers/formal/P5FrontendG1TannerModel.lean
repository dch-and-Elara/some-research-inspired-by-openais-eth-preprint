import P5FrontendG1Literal

/-! The printed source's two copies of the binary shift graph. An edge is
a left word and a port, not a pair of distinct endpoints: repetitions of
a shift do not identify edge occurrences. A row is an indexed check, not
a deduplicated equation. -/
namespace Paper5.FrontendG1.Tanner
open scoped BigOperators

abbrev Word (ell : ℕ) := Fin ell → F₂
abbrev Edge (ell d : ℕ) := Word ell × Fin d
abbrev Row (ell c : ℕ) := (Word ell × Fin c) ⊕ (Word ell × Fin c)

def rightEndpoint {ell d : ℕ} (s : Fin d→Word ell) (e : Edge ell d) : Word ell :=
  e.1+s e.2

def edgeAtRight {ell d : ℕ} (s : Fin d→Word ell) (u : Word ell) (j : Fin d) :
    Edge ell d := (u+s j,j)

private theorem f2_two (b : F₂) : b+b=0 := by
  revert b
  decide

theorem rightEndpoint_atRight {ell d : ℕ} (s : Fin d→Word ell) (u : Word ell) (j : Fin d) :
    rightEndpoint s (edgeAtRight s u j)=u := by
  ext k
  change (u k+s j k)+s j k=u k
  rw [add_assoc,f2_two,add_zero]

theorem edge_atRight_rightEndpoint {ell d : ℕ} (s : Fin d→Word ell) (e : Edge ell d) :
    edgeAtRight s (rightEndpoint s e) e.2=e := by
  refine Prod.ext ?_ ?_
  · funext k
    change (e.1 k+s e.2 k)+s e.2 k=e.1 k
    rw [add_assoc,f2_two,add_zero]
  · rfl

def entry {ell d c : ℕ} (s : Fin d→Word ell) (A : Matrix (Fin c) (Fin d) F₂)
    (r : Row ell c) (e : Edge ell d) : F₂ :=
  match r with
  | .inl (u,i) => if u=e.1 then A i e.2 else 0
  | .inr (v,i) => if v=rightEndpoint s e then A i e.2 else 0

def shortened {C : Type*} {ell d c : ℕ} (s : Fin d→Word ell)
    (A : Matrix (Fin c) (Fin d) F₂) (keep : C↪Edge ell d) : Matrix (Row ell c) C F₂ :=
  fun r i => entry s A r (keep i)

noncomputable def extendZeros {C : Type*} {ell d : ℕ} (keep : C↪Edge ell d) (x : C→F₂) :
    Edge ell d→F₂ :=
  Function.extend keep x fun _=>0

theorem extendZeros_kept {C : Type*} {ell d : ℕ} (keep : C↪Edge ell d)
    (x : C→F₂) (i : C) : extendZeros keep x (keep i)=x i :=
  keep.injective.extend_apply _ _ _

theorem extendZeros_outside {C : Type*} {ell d : ℕ} (keep : C↪Edge ell d) (x : C→F₂)
    (e : Edge ell d) (h : ¬ ∃ i, keep i=e) : extendZeros keep x e=0 :=
  Function.extend_apply' _ _ _ h

theorem shortened_eq_full_zero_extension {C : Type*} [Fintype C] {ell d c : ℕ}
    (s : Fin d→Word ell) (A : Matrix (Fin c) (Fin d) F₂) (keep : C↪Edge ell d) (x : C→F₂) :
    (shortened s A (Function.Embedding.refl (Edge ell d))).mulVec (extendZeros keep x) =
       (shortened s A keep).mulVec x := by
  classical
  funext r
  change (∑ e : Edge ell d, entry s A r e * extendZeros keep x e) =
    ∑ i : C, entry s A r (keep i) * x i
  calc
    _ = ∑ e ∈ Finset.univ.map keep, entry s A r e * extendZeros keep x e := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro e _ h
      have hh : ¬ ∃ i, keep i=e := by simpa using h
      rw [extendZeros_outside keep x e hh,mul_zero]
    _ = _ := by rw [Finset.sum_map]; simp [extendZeros_kept]

def support {W : Type*} [Fintype W] (x : W→F₂) : Finset W :=
  Finset.univ.filter fun w=>x w≠0

def weight {W : Type*} [Fintype W] (x : W→F₂) : ℕ := (support x).card

theorem indexed_row_width {C : Type*} [Fintype C] {ell d c : ℕ}
    (s : Fin d→Word ell) (A : Matrix (Fin c) (Fin d) F₂)
    (keep : C↪Edge ell d) (r : Row ell c) : weight (shortened s A keep r)≤d := by
  classical
  let f : ↥(support (shortened s A keep r))→Fin d := fun i=>(keep i.val).2
  have nz (i : ↥(support (shortened s A keep r))) :
      entry s A r (keep i.val)≠0 := (Finset.mem_filter.mp i.property).2
  have hi : Function.Injective f := by
    intro i j hp
    have hj : (keep i.val).2=(keep j.val).2 := hp
    apply Subtype.ext
    apply keep.injective
    rcases r with ⟨u,k⟩|⟨u,k⟩
    · have eqL (t : ↥(support (shortened s A keep (Sum.inl (u,k))))) :
          u=(keep t.val).1 := by
        by_contra h
        have z := nz t
        exact z (by simp [entry,h])
      exact Prod.ext ((eqL i).symm.trans (eqL j)) hj
    · have eqR (t : ↥(support (shortened s A keep (Sum.inr (u,k))))) :
          u=rightEndpoint s (keep t.val) := by
        by_contra h
        have z := nz t
        exact z (by simp [entry,h])
      rw [←edge_atRight_rightEndpoint s (keep i.val),←edge_atRight_rightEndpoint s (keep j.val),
        ←eqR i,←eqR j,hj]
  simpa [weight] using Fintype.card_le_of_injective f hi

def LocalDistance {d c : ℕ} (A : Matrix (Fin c) (Fin d) F₂) (D : ℚ) : Prop :=
  ∀ x : Fin d→F₂, x≠0 → A.mulVec x=0 → D≤(weight x:ℚ)

def singlePort {d : ℕ} (j : Fin d) : Fin d→F₂ :=
  fun k=>if k=j then 1 else 0

theorem singlePort_support {d : ℕ} (j : Fin d) : support (singlePort j)={j} := by
  ext k
  simp [support,singlePort]

private theorem f2_zero_or_one : ∀ b : F₂, b=0 ∨ b=1 := by decide

theorem local_column_has_one {d c : ℕ} (A : Matrix (Fin c) (Fin d) F₂)
    (D : ℚ) (hD : 1<D) (dist : LocalDistance A D) (j : Fin d) :
    ∃ i : Fin c, A i j=1 := by
  by_contra! h
  have hz (i : Fin c) : A i j=0 := (f2_zero_or_one _).resolve_right (h i)
  have hKernel : A.mulVec (singlePort j)=0 := by
    funext i
    change (∑ k : Fin d, A i k * singlePort j k)=0
    simp [singlePort,mul_ite,hz]
  have hNonzero : singlePort j≠0 := by
    intro hh
    have hJ := congrFun hh j
    simp [singlePort] at hJ
  have hb := dist (singlePort j) hNonzero hKernel
  rw [weight,singlePort_support,Finset.card_singleton,Nat.cast_one] at hb
  exact (not_le_of_gt hD) hb

/-- The identical local witness may be used at both ends; the *row indices*
are different even if the shortened vectors coincide. -/
theorem opposite_indexed_rows {C : Type*} {ell d c : ℕ}
    (s : Fin d→Word ell) (A : Matrix (Fin c) (Fin d) F₂) (keep : C↪Edge ell d)
    (D : ℚ) (hD : 1<D) (dist : LocalDistance A D) (i : C) :
    ∃ j : Fin c,
      let r₁ : Row ell c := .inl ((keep i).1,j)
      let r₂ : Row ell c := .inr (rightEndpoint s (keep i),j)
      r₁≠r₂ ∧ shortened s A keep r₁ i=1 ∧ shortened s A keep r₂ i=1 := by
  obtain ⟨j,hj⟩ := local_column_has_one A D hD dist (keep i).2
  exact ⟨j,by simp [shortened,entry,hj]⟩

#print axioms rightEndpoint_atRight
#print axioms edge_atRight_rightEndpoint
#print axioms extendZeros_kept
#print axioms extendZeros_outside
#print axioms shortened_eq_full_zero_extension
#print axioms indexed_row_width
#print axioms singlePort_support
#print axioms local_column_has_one
#print axioms opposite_indexed_rows
end Paper5.FrontendG1.Tanner