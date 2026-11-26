import P5HybridClosureScan

/-! §8 common exact-cost terminal lemma. The two coordinates are projections of
one supplied pin word in one layout; no native interpolation value is assumed.
The alignment and legality of the actual layout are separate lemmas. -/
namespace Paper5.HybridClosure
open scoped Classical
variable {V I A : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
theorem first_coordinate_local (pin : TriVertex V → I → A) (i : I) (c : V → A)
    (h : ∀ p, pin p i = mainPinColor c p) :
    ∀ e ∈ innerEdges V, pin e.1 i = pin e.2 i := by
  intro e he
  rw [h,h]
  exact main_inner_monochromatic c e he

omit [Fintype V] [Fintype A] [DecidableEq A] in
theorem second_coordinate_local (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v = 3)
    (pin : TriVertex V → I → A) (j : I) (c : E → A)
    (h : ∀ p, pin p j = dPinColor E cubic c p) :
    ∀ e ∈ outerEdges E cubic, pin e.1 j = pin e.2 j := by
  intro e he
  rw [h,h]
  exact d_outer_monochromatic E cubic c e he

noncomputable def sameRouteScan (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v = 3)
    (pin : TriVertex V → I → A) (i j : I) (c : V → A) (d : E → A)
    (hi : ∀ p, pin p i = mainPinColor c p)
    (hj : ∀ p, pin p j = dPinColor E cubic d p) (σ : TriVertex V → Bool) :
    Bool × ℕ :=
  let a := completeFamily (innerEdges V) (fun p => pin p i)
    (first_coordinate_local pin i c hi) σ
  let b := completeFamily (outerEdges E cubic) (fun p => pin p j)
    (second_coordinate_local E cubic pin j d hj) σ
  (a.1 && b.1, a.2+b.2+1)

theorem sameRouteScan_exact (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v = 3)
    (loopless : ∀ v, (v,v) ∉ E) (pin : TriVertex V → I → A)
    (i j : I) (c : V → A) (d : E → A)
    (hi : ∀ p, pin p i = mainPinColor c p)
    (hj : ∀ p, pin p j = dPinColor E cubic d p)
    (left right : replacedEdges E cubic → Fin 4) (σ : TriVertex V → Bool) :
    boolAsNat (sameRouteScan E cubic pin i j c d hi hj σ).1 =
      PinnedCNF.modelCount (MainClonedCNF.formula (replacedEdges E cubic) left right σ) ∧
    (sameRouteScan E cubic pin i j c d hi hj σ).2 =
      6*Fintype.card (TriVertex V)+2*Fintype.card A+1 := by
  have hi' : (fun p => pin p i)=mainPinColor c := funext hi
  have hj' : (fun p => pin p j)=dPinColor E cubic d := funext hj
  have hs : sameRouteScan E cubic pin i j c d hi hj σ=twoMethodScan E cubic c d σ := by
    unfold sameRouteScan twoMethodScan
    simp only [hi',hj']
  rw [hs]
  obtain ⟨hcnt,hfee⟩ := twoMethodScan_exact E cubic loopless c d left right σ
  exact ⟨hcnt,by omega⟩

#print axioms first_coordinate_local
#print axioms second_coordinate_local
#print axioms sameRouteScan
#print axioms sameRouteScan_exact
end Paper5.HybridClosure
