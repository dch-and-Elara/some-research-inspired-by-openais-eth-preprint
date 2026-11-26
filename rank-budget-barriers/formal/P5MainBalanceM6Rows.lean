import P5MainBalanceSourceFiber
import Mathlib.Algebra.Polynomial.BigOperators

/-! Literal MAIN row construction (OpenAI §5, equations
coefficient-correction, swaps-row, actual-rows and actual-measurements).
The group base comes from the placed vector and the (I-M₀) term,
not from an assumed group-local evaluation table. -/
namespace P5MainBalance.M6
open P5MainIterator Polynomial
open scoped BigOperators Classical

variable {E W F Copy I B : Type*} [Fintype E] [Fintype W] [Fintype Copy]
  [Fintype I] [Fintype B] [LinearOrder B]

abbrev Slt (Copy I B : Type*) [LinearOrder B] := CopiedSlot Copy I B
abbrev Vec (Copy I B : Type*) [LinearOrder B] := Slt Copy I B → ℚ
abbrev Mix (Copy I B : Type*) [LinearOrder B] :=
  Matrix (Slt Copy I B) (Slt Copy I B) ℚ

noncomputable def phys (s : Slt Copy I B) : Copy × WordCell I B := copyDecode s
noncomputable def atNode (t : I→ℚ) (u v : Slt Copy I B) : ℚ[X] :=
  ∏ i,if ((phys v).2 i).1 = ((phys u).2 i).2 then 1 else 1-X*C (t i)⁻¹

omit [Fintype E] [Fintype W] [Fintype Copy] [Fintype B] in
theorem atNode_zero (t : I→ℚ) (u v : Slt Copy I B) :
    (atNode t u v).eval 0=1 := by
  unfold atNode
  rw [eval_prod]
  exact Finset.prod_eq_one fun i _ => by split <;> simp

omit [Fintype E] [Fintype W] [Fintype Copy] [Fintype B] in
theorem atNode_off (t : I→ℚ) (i : I) (hi : t i≠0)
    (u v : Slt Copy I B) (h : ((phys v).2 i).1 ≠ ((phys u).2 i).2) :
    (atNode t u v).eval (t i)=0 := by
  unfold atNode
  rw [eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h,hi])

noncomputable def place (L : SourceLayout E W F Copy I B) (x : W→ℚ) :
    Vec Copy I B := (embeddingMatrix CoordFamily L.orbitPlacement).mulVec x

noncomputable def slotOf (L : SourceLayout E W F Copy I B) (e : E) : Slt Copy I B :=
  copyEncode (L.placement.slot e)

omit [Fintype E] [Fintype W] [Fintype Copy] [Fintype I] [Fintype B] in
@[simp] theorem phys_slotOf (L : SourceLayout E W F Copy I B) (e : E) :
    phys (slotOf L e)=L.placement.slot e := copy_decode_encode _

omit [Fintype Copy] [Fintype B] in
theorem place_at (L : SourceLayout E W F Copy I B) (x : W→ℚ) (e : E) :
    place L x (slotOf L e)=x (L.placement.owner e) := by
  unfold place
  rw [Matrix.mulVec,dotProduct,Finset.sum_eq_single (L.placement.owner e)]
  · have he : slotOf L e∈filled L.orbitPlacement (L.placement.owner e) := by
      exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩
    simp [embeddingMatrix,he]
  · intro v _ hv
    have hn : slotOf L e∉filled L.orbitPlacement v := by
      intro h
      obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
      have heq : z=e := L.orbitPlacement.slot.injective he
      exact hv ((Finset.mem_filter.mp hz).2.symm.trans (congrArg L.placement.owner heq))
    simp [embeddingMatrix,hn]
  · simp

omit [Fintype Copy] [Fintype B] in
theorem place_local (L : SourceLayout E W F Copy I B) (i : I) (g : B)
    (x y : W→ℚ) (h : ∀ w,L.a w i=g → x w=y w) (s : Slt Copy I B)
    (hs : ((phys s).2 i).1=g) : place L x s=place L y s := by
  unfold place
  simp only [Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro w _
  by_cases H : s∈filled L.orbitPlacement w
  · obtain ⟨e,he,hes⟩ := Finset.mem_image.mp H
    have hw := (Finset.mem_filter.mp he).2
    have hp : slotOf L e=s := hes
    have hh : L.a w i=g := by
      rw [←hw]
      change L.a (L.placement.owner e) i=g
      exact (L.first e i).symm.trans (by rw [←phys_slotOf L e,hp]; exact hs)
    rw [h w hh]
  · simp [embeddingMatrix,H]

noncomputable def rowChart (t : I→ℚ) (M : Mix Copy I B) (u : Slt Copy I B)
    (ζ : Vec Copy I B) : ℚ[X] :=
  C (ζ u - M.mulVec ζ u) +
    ∑ v,C (M u v*ζ v)*atNode t u v

theorem rowChart_zero (t : I→ℚ) (M : Mix Copy I B) (u : Slt Copy I B)
    (ζ : Vec Copy I B) : (rowChart t M u ζ).eval 0=ζ u := by
  unfold rowChart
  simp [eval_finset_sum, atNode_zero, Matrix.mulVec,dotProduct]

/-- The physical polynomial from the original copied swap row. -/
noncomputable def physicalRow (L : SourceLayout E W F Copy I B) (t : I→ℚ)
    (M : Mix Copy I B) (e : E) (x : W→ℚ) : ℚ[X] :=
  rowChart t M (slotOf L e) (place L x)

theorem physicalRow_zero (L : SourceLayout E W F Copy I B) (t : I→ℚ)
    (M : Mix Copy I B) (e : E) (x : W→ℚ) :
    (physicalRow L t M e x).eval 0=x (L.placement.owner e) := by
  rw [physicalRow,rowChart_zero,place_at]

def qbits (x : W→Bool) : W→ℚ := BooleanMeasurement.bit ℚ ∘ x

noncomputable def nativeMask (L : SourceLayout E W F Copy I B) (i : I) (g : B)
    (x : W→Bool) (w : W) : ℚ := if L.a w i=g then qbits x w else 0

omit [Fintype E] [Fintype W] [Fintype Copy] [Fintype I] in
theorem group_mask_sum (L : SourceLayout E W F Copy I B) (i : I) (x : W→Bool) :
    (∑ g,nativeMask L i g x)=qbits x := by
  funext w
  rw [Finset.sum_apply]
  change (∑ g,if L.a w i=g then qbits x w else 0)=_
  simp

/-- Exactly the native swap-kernel certificate, before its physical
copy, evaluation and sign-ownership consequences. -/
def FixesKernel (keep : ℕ→Prop) (M : Mix Copy I B) : Prop :=
  ∀ ζ : Vec Copy I B,(rawRows CoordFamily keep).mulVec ζ=0 → M.mulVec ζ=ζ

/-- The precise remaining equal-measurement implication for the
(I-M₀) term, before the fully spectral certificate is inserted. -/
def ActualBaseInvariant (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (M : Mix Copy I B) : Prop :=
  ∀ (i : I) (x y : W→Bool),
    sourceTuple keep L i x=sourceTuple keep L i y →
    ∀ s : Slt Copy I B,place L (qbits x) s - M.mulVec (place L (qbits x)) s =
      place L (qbits y) s - M.mulVec (place L (qbits y)) s

/-- Source row locality: conditioning on all raw measurements and the
one chosen assignment group is sufficient for every incidence in the
factor's group. The φ polynomials eliminate the other entries. -/
theorem current_actual_row_local (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (t : I→ℚ) (M : Mix Copy I B) (hM : ActualBaseInvariant keep L M)
    (i : I) (hi : t i≠0) (e : E) (x y : W→Bool)
    (hy : sourceTuple keep L i x=sourceTuple keep L i y)
    (hx : ∀ w,L.a w i=L.d (L.factor e) i → x w=y w) :
    (physicalRow L t M e (qbits x)).eval (t i)=
      (physicalRow L t M e (qbits y)).eval (t i) := by
  unfold physicalRow rowChart
  simp only [eval_add,eval_C,eval_finset_sum,eval_mul]
  rw [hM i x y hy]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : ((phys v).2 i).1=((phys (slotOf L e)).2 i).2
  · have h' : ((phys v).2 i).1=L.d (L.factor e) i := h.trans (by rw [phys_slotOf,L.second])
    have hl : place L (qbits x) v=place L (qbits y) v := place_local L i _ (qbits x) (qbits y)
      (fun w hw=>congrArg (BooleanMeasurement.bit ℚ) (hx w hw)) v h'
    rw [hl]
  · simp [atNode_off t i hi _ _ h]

#print axioms atNode_off
#print axioms place_at
#print axioms rowChart_zero
#print axioms physicalRow_zero
#print axioms current_actual_row_local
end P5MainBalance.M6
