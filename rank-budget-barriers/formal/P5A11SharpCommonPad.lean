import P5A11SharpCommonReduction
import P5A10Full
import Mathlib.Data.Fin.Rev
import Mathlib.Data.ENat.Basic

/-! Sort the finite Smith valuations, append actual zero invariant
factors as infinity, then reverse the order for truncated lengths. -/
namespace Paper5.CommonJets
open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

noncomputable def paddedValuations {r n : ℕ} (σ : Fin r→ℕ) (i : Fin n) : ENat :=
  if h : i.val<r then (σ ⟨i.val,h⟩:ENat) else ⊤

theorem padded_order {r n : ℕ} (σ : Fin r→ℕ) (hs : Monotone σ) :
    Monotone (paddedValuations (n:=n) σ) := by
  intro i j hij
  by_cases hj : j.val<r
  · have hi : i.val<r := lt_of_le_of_lt hij hj
    rw [paddedValuations,paddedValuations,dif_pos hi,dif_pos hj]
    have hh : σ ⟨i.val,hi⟩≤σ ⟨j.val,hj⟩ := hs hij
    exact_mod_cast hh
  · have hj' : paddedValuations σ j=(⊤:ENat) := dif_neg hj
    rw [hj']
    exact le_top

noncomputable def clipped (P : ℕ) (s : ENat) : ℕ := ((P:ENat)-s).toNat

@[simp] theorem clipped_coe (P s : ℕ) : clipped P (s:ENat)=P-s := by
  rw [clipped,←ENat.coe_sub,ENat.toNat_coe]

@[simp] theorem clipped_top (P : ℕ) : clipped P ⊤=0 := by simp [clipped]

theorem clipped_antitone (P : ℕ) : Antitone (clipped P) := by
  intro s t h
  exact ENat.toNat_le_toNat (tsub_le_tsub_left h (P:ENat))
    (ne_top_of_le_ne_top (ENat.coe_ne_top P) tsub_le_self)

noncomputable def appendCyclicZero (π : R) {r : ℕ} (q : Fin r→ℕ) (z : ℕ) :
    CyclicGrid π q ≃ₗ[R] CyclicGrid π (Sum.elim q (fun (_ : Fin z)=>0)) := by
  let f : CyclicGrid π q →ₗ[R] CyclicGrid π (Sum.elim q (fun (_ : Fin z)=>0)) :=
    LinearMap.pi fun j => match j with
      | .inl i => LinearMap.proj i
      | .inr _ => 0
  apply LinearEquiv.ofBijective f
  constructor
  · intro a b h
    funext i
    exact congrFun h (Sum.inl i)
  · intro y
    refine ⟨fun i=>y (.inl i),?_⟩
    funext j
    cases j with
    | inl i => rfl
    | inr i =>
      exact (zero_of_cyclic_zero π (y (.inr i))).symm

noncomputable def appendPadded {r n : ℕ} (hr : r≤n) (π : R) (P : ℕ) (σ : Fin r→ℕ) :
    CyclicGrid π (fun i=>P-σ i) ≃ₗ[R]
      CyclicGrid π (fun i : Fin n=>clipped P (paddedValuations σ i)) := by
  let F : Fin r ⊕ Fin (n-r) ≃ Fin n := finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hr))
  have hq : Sum.elim (fun i=>P-σ i) (fun (_:Fin (n-r))=>0) =
      (fun j => clipped P (paddedValuations σ (F j))) := by
    funext j
    cases j with
    | inl i =>
      have hi : (F (.inl i)).val<r := i.isLt
      rw [paddedValuations,dif_pos hi,clipped_coe]
      rfl
    | inr i =>
      have hi : ¬(F (.inr i)).val<r := by
        change ¬r+i.val<r
        omega
      rw [paddedValuations,dif_neg hi,clipped_top]
      rfl
  have eq : CyclicGrid π (fun i=>P-σ i) ≃ₗ[R]
      CyclicGrid π (fun j=>clipped P (paddedValuations σ (F j))) := by
    exact cast (congrArg (fun Q : (Fin r ⊕ Fin (n-r))→ℕ =>
      CyclicGrid π (fun i=>P-σ i) ≃ₗ[R] CyclicGrid π Q) hq)
      (appendCyclicZero π (fun i=>P-σ i) (n-r))
  exact eq.trans (LinearEquiv.piCongrLeft R (fun i : Fin n=>
    Cyclic π (clipped P (paddedValuations σ i))) F)

noncomputable def sortPadReverse {r n : ℕ} (hr : r≤n) (π : R) (P : ℕ)
    (σ : Fin r→ℕ) (e : Equiv.Perm (Fin r)) :
    CyclicGrid π (fun i=>P-σ i) ≃ₗ[R]
      CyclicGrid π (fun i : Fin n=>clipped P (paddedValuations (σ∘e) i.rev)) := by
  let s : Fin n→ℕ := fun i=>clipped P (paddedValuations (σ∘e) i)
  let E : CyclicGrid π (fun i=>P-σ i) ≃ₗ[R] CyclicGrid π (fun i=>P-(σ∘e) i) :=
    (LinearEquiv.piCongrLeft R (fun i=>Cyclic π (P-σ i)) e).symm
  exact E.trans ((appendPadded hr π P (σ∘e)).trans
    (LinearEquiv.piCongrLeft R (fun i=>Cyclic π (s i)) Fin.revPerm).symm)

theorem reversed_clipped_order {r n : ℕ} (P : ℕ) (σ : Fin r→ℕ) (hs : Monotone σ) :
    Monotone (fun i : Fin n=>clipped P (paddedValuations σ i.rev)) := by
  intro i j h
  apply clipped_antitone
  apply padded_order σ hs
  simpa only [Fin.rev_le_rev] using h

#print axioms padded_order
#print axioms clipped_coe
#print axioms clipped_top
#print axioms clipped_antitone
#print axioms appendCyclicZero
#print axioms appendPadded
#print axioms sortPadReverse
#print axioms reversed_clipped_order
end Paper5.CommonJets
