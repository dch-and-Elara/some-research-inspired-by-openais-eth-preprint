import J6R10RepackState
import J6R10IntegralPhysical

/-! Match literal parent tensors to the retained old tables used by
the physical mode sum. Every tensor is lifted from its own creation
precision, not by reducing and recanonicalizing the parent product. -/
namespace J6R11Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Repack J6R10Integral
open J6R9PacketScopes J6R9PacketChild P11FullPacking

variable {E A B G : Type*} [LinearOrder G] [Fintype G] {a : ℕ}
variable {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

def mixedAssignment (N : Network E A B) (Y X : E → Bool) (v : A ⊕ B) :
    ParentPorts N v → Bool := fun p => Sum.elim Y X p.val

omit [LinearOrder G] [Fintype G] in
theorem mixed_eq_row (N : Network E A B) (Y X : E → Bool) (v : A) :
    mixedAssignment N Y X (.inl v) = assignment N Y (.inl v) := by
  funext p
  rcases p with ⟨p,hp⟩
  cases p with
  | inl e => rfl
  | inr e => exact nomatch hp

omit [LinearOrder G] [Fintype G] in
theorem mixed_eq_col (N : Network E A B) (Y X : E → Bool) (v : B) :
    mixedAssignment N Y X (.inr v) = assignment N X (.inr v) := by
  funext p
  rcases p with ⟨p,hp⟩
  cases p with
  | inl e => exact nomatch hp
  | inr e => rfl

def rowGroupAt (P : PhysicalPacking N a G) (i : Fin a) (e : E) : G :=
  rowGroup P.mask i (P.seat e)

def colGroupAt (P : PhysicalPacking N a G) (i : Fin a) (e : E) : G :=
  colGroup P.mask i (P.seat e)

theorem retained_reads_mixed (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (v : Old (atGroup P i) g) (Y X : E → Bool) :
    restrictOriginal N (atGroup P i) g v
      ((stateEquiv P i g).symm
        (pairedGroups (Equiv.refl E) (rowGroupAt P i) (colGroupAt P i) (Y,X) g)) =
      mixedAssignment N Y X v.val := by
  let s := pairedGroups (Equiv.refl E) (rowGroupAt P i) (colGroupAt P i) (Y,X) g
  let z := (stateEquiv P i g).symm s
  have ez : stateEquiv P i g z = s := (stateEquiv P i g).apply_symm_apply s
  funext h
  rcases h with ⟨p,hp⟩
  cases p with
  | inl e =>
    have hg := (congrArg (atGroup P i) hp).trans v.property
    have he := (row_symbol P i e).trans hg
    change z ⟨.inl e,hg⟩ = Y e
    exact ((state_reads_row P i g z e he).symm.trans
      (congrArg (fun s' : PhysicalState P i g => s'.1 ⟨e,he⟩) ez))
  | inr e =>
    have hg := (congrArg (atGroup P i) hp).trans v.property
    have he := (col_symbol P i e).trans hg
    change z ⟨.inr e,hg⟩ = X e
    exact ((state_reads_col P i g z e he).symm.trans
      (congrArg (fun s' : PhysicalState P i g => s'.2 ⟨e,he⟩) ez))

section TensorProduct
variable [Fintype A] [Fintype B]

noncomputable def rowProduct (N : Network E A B) (file : EntryFile f ell N)
    (hf : f.Monic) (Y : E → Bool) : IntRing f ell :=
  ∏ v : A, (file (.inl v)).frozen hf (assignment N Y (.inl v))

noncomputable def colProduct (N : Network E A B) (file : EntryFile f ell N)
    (hf : f.Monic) (X : E → Bool) : IntRing f ell :=
  ∏ v : B, (file (.inr v)).frozen hf (assignment N X (.inr v))

noncomputable def mixingProduct (N : Network E A B) (file : EntryFile f ell N)
    (hf : f.Monic) (Y X : E → Bool) : IntRing f ell :=
  ∏ v : A ⊕ B, (file v).frozen hf (mixedAssignment N Y X v)

omit [LinearOrder G] [Fintype G] in
theorem mixingProduct_split (N : Network E A B) (file : EntryFile f ell N)
    (hf : f.Monic) (Y X : E → Bool) :
    mixingProduct N file hf Y X = rowProduct N file hf Y * colProduct N file hf X := by
  unfold mixingProduct rowProduct colProduct
  rw [Fintype.prod_sum_type]
  simp only [mixed_eq_row,mixed_eq_col]

theorem oldState_factors (P : PhysicalPacking N a G) (i : Fin a) (p : ℕ)
    (file : EntryFile f ell N) (hf : f.Monic) (Y X : E → Bool) :
    reduce p f ell (rowProduct N file hf Y) * reduce p f ell (colProduct N file hf X) =
      ∏ g, oldState P i g p file hf
        (pairedGroups (Equiv.refl E) (rowGroupAt P i) (colGroupAt P i) (Y,X) g) := by
  classical
  rw [← map_mul,← mixingProduct_split,mixingProduct,map_prod,
    J6BlockFactor.prod_rows (atGroup P i)]
  apply Finset.prod_congr rfl
  intro g _
  unfold oldState
  refine Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun v _ => ?_)
  rw [retained_reads_mixed]
  rfl

omit [LinearOrder G] [Fintype G] in
theorem mixed_diagonal (N : Network E A B) (file : EntryFile f ell N)
    (hf : f.Monic) (x : E → Bool) :
    rowProduct N file hf x * colProduct N file hf x =
      ∏ v : A ⊕ B, (file v).frozen hf (assignment N x v) := by
  rw [← mixingProduct_split,mixingProduct]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rcases v with v | v
  · rw [mixed_eq_row]
  · rw [mixed_eq_col]

end TensorProduct

#print axioms mixed_eq_row
#print axioms mixed_eq_col
#print axioms retained_reads_mixed
#print axioms mixingProduct_split
#print axioms oldState_factors
#print axioms mixed_diagonal
end J6R11Integral
