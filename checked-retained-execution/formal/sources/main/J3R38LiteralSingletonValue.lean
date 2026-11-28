import J3R38LiteralSingletonAlgebra

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6200000

/-! A query on the original MAIN register, on one graph-fixed physical
seating and one public replacement family.  Every requested direction has
its literal E=U={i}, and the measurement is computed at the all-one word
using the original per-copy integer row operator. -/
namespace J3R38LiteralSingleton
open Polynomial V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N1
open V8NativeMessage.N6.MainFiber
open scoped Polynomial BigOperators Classical

noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

abbrev Address (W : Type*) (Q : ℕ) := Fin Q × Clone W
abbrev Replacement {W : Type*} (F : Finset (W×W)) := Clause F → Clone W → Clone W → ℚ[X]

def literalTuple (P : Seating F Copy r Q hreg) (R : ℕ) (hJ : 2≤J)
    (Prow : Replacement F) (a : Address W Q) : CloneTuple F r Q J where
  frame := sourceFrame (printedRows r Q R) P a.1 {a.2} (allOneAddress (printedRows r Q R) P a.1)
  node := a.1
  U := {a.2}
  correction_subset := Finset.Subset.rfl
  correction_order := by simpa only [sourceFrame,Finset.card_singleton] using
    (show 1≤J-1 by omega)
  factorGroup c := P.factorLabel c a.1
  replacement := Prow

theorem original_menu (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2≤J) (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q) (a : Address W Q) :
    let L := literalTuple P R hJ Prow a
    L.frame.E = {a.2} ∧ L.U = {a.2} ∧
      (∀ g j, |L.frame.y g j| ≤ ((r^(2*Q):ℕ):ℤ)) ∧ feasible L.frame ∧
      ∀ g, (∀ x, unrestricted L.frame g x ↔ x=oneWord L.frame g) ∧
        (Finset.univ : Finset (Word L.frame g)).filter (eligible L.frame g) = {oneWord L.frame g} := by
  exact ⟨rfl,rfl,printed_MAIN_one hreg P (literalTuple P R hJ Prow a) hr hR hfit rfl⟩

theorem merge_all_one {V G : Type*} [Fintype V] (f : Frame V G) (h : feasible f)
    (hw : ∀ g x, unrestricted f g x ↔ x=oneWord f g) (g : G) :
    merge f (repWord f h) g (oneWord f g) = fun _ => true := by
  funext v
  unfold merge
  split
  · rfl
  · rw [(hw _ _).1 (repWord_unrestricted f h _)]
    rfl

theorem actual_completed_at_one (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2≤J) (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q) (a : Address W Q) (s : W→Bool) :
    let L := literalTuple P R hJ Prow a
    (nativeScan F hreg L s).2.2 = ∏ c : Clause F, cloneFactor F hreg L s (fun _=>true) c := by
  let L := literalTuple P R hJ Prow a
  obtain ⟨_,_,_,hf,hg⟩ := original_menu P Prow hJ hr hR hfit a
  change (nativeScan F hreg L s).2.2 = _
  rw [native_value_uses_representatives F hreg L s hf]
  calc
    _ = ∏ g : Fin r, nativeGroup F hreg L s g (fun _=>true) := by
      apply Finset.prod_congr rfl
      intro g _
      rw [(hg g).2, Finset.sum_singleton, merge_all_one L.frame hf (fun g => (hg g).1) g]
    _ = _ := Finset.prod_fiberwise Finset.univ L.factorGroup
      (cloneFactor F hreg L s (fun _=>true))

def rowAtOne (L : CloneTuple F r Q J) (reg : ∀ v, GraphCutMoments.degree F v=3) (o : Occ F) : ℚ[X] := thetaPoly L reg (fun _=>true) o

def publicFactor (L : CloneTuple F r Q J) (reg : ∀ v, GraphCutMoments.degree F v=3) : F ⊕ Clone W → ℚ[X]
  | .inl e => 1 - (1 - rowAtOne L reg (.inr (.inl (e,true)))) *
      (1 - rowAtOne L reg (.inr (.inl (e,false))))
  | .inr i => 1 - rowAtOne L reg (.inr (.inr (i,true))) *
      (1 - rowAtOne L reg (.inr (.inr (i,false))))

def backgroundPoly (L : CloneTuple F r Q J) (reg : ∀ v, GraphCutMoments.degree F v=3) : ℚ[X] := ∏ f : F ⊕ Clone W, publicFactor L reg f

def onePointProduct (L : CloneTuple F r Q J) (reg : ∀ v, GraphCutMoments.degree F v=3) (s : W→Bool) : ℚ[X] :=
  backgroundPoly L reg *
    ∏ v : W, JointContraction.pinPolynomial (s v) (rowAtOne L reg (.inl v))

theorem mk_onePointProduct (L : CloneTuple F r Q J) (reg : ∀ v, GraphCutMoments.degree F v=3) (s : W→Bool) :
    (AdjoinRoot.mk _ (onePointProduct L reg s) : Jet J) =
      ∏ f : Clause F, cloneFactor F reg L s (fun _=>true) f := by
  rw [onePointProduct, Fintype.prod_sum_type, mul_comm]
  simp only [backgroundPoly,map_mul,map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    cases hv : s v <;> simp [JointContraction.pinPolynomial,rowAtOne,thetaPoly_mk,cloneFactor,
      signedLiteral,occClause,occVar,hv]
  · apply Finset.prod_congr rfl
    intro f _
    cases f with
    | inl e => simp [publicFactor,rowAtOne,thetaPoly_mk,cloneFactor,occClause,occVar]
    | inr i => rcases i with ⟨v,j⟩
               simp [publicFactor,rowAtOne,thetaPoly_mk,cloneFactor,occClause,occVar]

theorem true_jet_from_one_point (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2≤J) (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q) (a : Address W Q) (s : W→Bool) :
    let T := literalTuple P R hJ Prow a
    (nativeScan F hreg T s).2.2 = (AdjoinRoot.mk _ (onePointProduct T hreg s) : Jet J) :=
  (actual_completed_at_one P Prow hJ hr hR hfit a s).trans
    (mk_onePointProduct (literalTuple P R hJ Prow a) hreg s).symm

#print axioms original_menu
#print axioms merge_all_one
#print axioms actual_completed_at_one
#print axioms mk_onePointProduct
#print axioms true_jet_from_one_point

end
end J3R38LiteralSingleton
