import BooleanCube.Layers
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Basis.Basic

namespace LocalReconstruction
open Polynomial
open scoped Polynomial
noncomputable section

def reindex {q : ℕ} (e : Equiv.Perm (Fin q)) (s : Cube q) : Cube q := fun i => s (e i)

def PermInvariant {q : ℕ} (W : Submodule ℚ (Cube q → ℚ)) : Prop :=
  ∀ e : Equiv.Perm (Fin q), ∀ f ∈ W, (fun x => f (reindex e x)) ∈ W

private theorem weight_reindex {q : ℕ} (e : Equiv.Perm (Fin q)) (s : Cube q) :
    weight (reindex e s) = weight s := by
  have eq : ones (reindex e s) = (ones s).map e.symm.toEmbedding := by
    ext j
    simp [ones,reindex]
  simp [weight, eq]

private theorem weight_orbit {q : ℕ} {s t : Cube q} (hw : weight s = weight t) :
    ∃ e : Equiv.Perm (Fin q), reindex e s = t := by
  classical
  let e : ↥(ones t) ≃ ↥(ones s) := Fintype.equivOfCardEq (by simpa [weight] using hw.symm)
  refine ⟨e.extendSubtype,?_⟩
  funext i
  by_cases h : i ∈ ones t
  · have hs := e.extendSubtype_mem i h
    simpa [ones,reindex] using (show s (e.extendSubtype i) = t i from
      ((Finset.mem_filter.mp hs).2).trans ((Finset.mem_filter.mp h).2).symm)
  · have hs := e.extendSubtype_not_mem i h
    change s (e.extendSubtype i) = t i
    simp only [ones,Finset.mem_filter,Finset.mem_univ,true_and,Bool.not_eq_true] at h hs
    rw [h,hs]

private theorem walsh_reindex {q : ℕ} (s : Cube q) (e : Equiv.Perm (Fin q)) :
    (fun x => walsh s (reindex e x)) = walsh (reindex e.symm s) := by
  funext x
  simpa [walsh,reindex] using Equiv.prod_comp e (fun j => signBit (s (e.symm j)) (x j))

private theorem mem_walshSpace {q : ℕ} {s : Cube q} {A : Set (Cube q)} :
    walsh s ∈ walshSpace A ↔ s ∈ A := by
  have he : (fun t => walshBasis q t) = walsh := funext (walshBasis_apply q)
  simpa only [walshSpace, ← he] using (walshBasis q).self_mem_span_image (i := s) (s := A)

theorem symmetric_spaces {q : ℕ} (W : Submodule ℚ (Cube q → ℚ)) :
    FlipInvariant W ∧ PermInvariant W ↔
      ∃ K : Finset ℕ, K ⊆ Finset.range (q+1) ∧ W = walshSpace (layerFamily q K) := by
  classical
  constructor
  · rintro ⟨hF,hP⟩
    obtain ⟨A, rfl⟩ := (flipInvariant_iff W).mp hF
    let K := A.toFinset.image weight
    have hA : A = layerFamily q K := by
      ext s
      change s ∈ A ↔ weight s ∈ A.toFinset.image weight
      constructor
      · exact fun h => Finset.mem_image_of_mem _ (Set.mem_toFinset.mpr h)
      · intro h
        obtain ⟨t,ht,he⟩ := Finset.mem_image.mp h
        obtain ⟨e,hw⟩ := weight_orbit he
        have hp := hP e.symm (walsh t) (mem_walshSpace.mpr (Set.mem_toFinset.mp ht))
        rw [walsh_reindex, Equiv.symm_symm,hw] at hp
        exact mem_walshSpace.mp hp
    refine ⟨K,?_,congrArg walshSpace hA⟩
    intro k hk
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    have h : weight s ≤ q := by simpa [weight] using Finset.card_le_univ (ones s)
    omega
  · rintro ⟨K,_,rfl⟩
    refine ⟨(flipInvariant_iff _).mpr ⟨_,rfl⟩,?_⟩
    intro e f hf
    induction hf using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨s,hs,rfl⟩ := hv
      rw [walsh_reindex]
      apply mem_walshSpace.mpr
      change weight (reindex e.symm s) ∈ K
      rwa [weight_reindex]
    | zero => exact (walshSpace _).zero_mem
    | add x y _ _ hx hy => exact (walshSpace _).add_mem hx hy
    | smul a x _ hx => exact (walshSpace _).smul_mem a hx

private def subsetEquiv (q : ℕ) : Cube q ≃ Finset (Fin q) where
  toFun := ones
  invFun := fun F i => decide (i ∈ F)
  left_inv s := by funext i; cases h : s i <;> simp [ones,h]
  right_inv F := by ext i; simp [ones]

theorem layer_size (q k : ℕ) :
    (Finset.univ.filter fun s : Cube q => weight s = k).card = q.choose k := by
  let e : {s : Cube q // weight s = k} ≃ {u : Finset (Fin q) // u.card = k} :=
    (subsetEquiv q).subtypeEquiv fun _ => Iff.rfl
  simpa [Fintype.subtype_card] using (Fintype.card_congr e).trans
    ((Fintype.card_finset_len (α := Fin q) k).trans (by simp))

theorem layer_rank (q : ℕ) (K : Finset ℕ) :
    Module.finrank ℚ (walshSpace (layerFamily q K)) = ∑ k ∈ K, q.choose k := by
  classical
  let A := layerFamily q K
  have hr : Set.range (fun s : A => walsh s.val) = walsh '' A := by ext; simp
  have hlin : LinearIndependent ℚ (fun s : A => walsh s.val) :=
    (walsh_independent q).comp _ Subtype.val_injective
  calc
    _ = Fintype.card A := by
      change Module.finrank ℚ (Submodule.span ℚ (walsh '' A)) = _
      rw [← hr]
      exact finrank_span_eq_card hlin
    _ = (Finset.univ.filter fun s : Cube q => weight s ∈ K).card := by
      rw [Fintype.subtype_card]
      congr 1
      ext s
      simp [A,layerFamily]
    _ = _ := by
      rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ K weight]
      simp_rw [layer_size]

def Ternary {ι κ : Type*} (C : Matrix ι κ ℚ) : Prop :=
  ∀ i j, C i j = -1 ∨ C i j = 0 ∨ C i j = 1

private theorem walsh_sign {q : ℕ} (s x : Cube q) : walsh s x = -1 ∨ walsh s x = 1 := by
  have H : walsh s x * walsh s x = 1 := by
    unfold walsh
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    cases s i <;> cases x i <;> norm_num [signBit]
  have h : (walsh s x + 1)*(walsh s x-1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h | h
  · left; linarith
  · right; linarith

def symmetricScheme (q b d : ℕ) (a : Fin q → ℚ) : Prop :=
  ∃ m ≤ b, ∃ C : Matrix (Fin m) (Cube q) ℚ, Ternary C ∧ FlipInvariant (rowSpace C) ∧
    PermInvariant (rowSpace C) ∧ ∃ P, matrixCondition a C d P

theorem symmetric_budget_iff {q b d : ℕ} {a : Fin q → ℚ}
    (hi : Function.Injective a) (hn : ∀ i, a i ≠ 0) :
    symmetricScheme q b d a ↔
      ∃ K : Finset ℕ, K ⊆ Finset.range (q+1) ∧
        (∑ k ∈ K, q.choose k) ≤ b ∧ gapsAtMost q d K := by
  classical
  constructor
  · rintro ⟨m,hm,C,_,hf,hp,hmat⟩
    obtain ⟨K,hK,hw⟩ := (symmetric_spaces _).mp ⟨hf,hp⟩
    refine ⟨K,hK,?_,(layers_iff_gaps hi hn K).mp ((matrix_iff_edges a C _ hw).mp hmat)⟩
    rw [← layer_rank, ← hw]
    exact (by simpa [rowSpace] using finrank_range_le_card (R := ℚ) C :
      Module.finrank ℚ (rowSpace C) ≤ m) |>.trans hm
  · rintro ⟨K,hK,hb,hgap⟩
    let A := layerFamily q K
    let e := Fintype.equivFin A
    let C : Matrix (Fin (Fintype.card A)) (Cube q) ℚ := fun i => walsh (e.symm i).val
    have hr : Set.range C = walsh '' A := by
      ext f
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨_,(e.symm i).property,rfl⟩
      · rintro ⟨s,hs,rfl⟩
        refine ⟨e ⟨s,hs⟩,?_⟩
        simp [C]
    have hw : rowSpace C = walshSpace A := congrArg (Submodule.span ℚ) hr
    have hc : Fintype.card A = ∑ k ∈ K, q.choose k := by
      rw [Fintype.subtype_card]
      calc
        _ = (Finset.univ.filter fun s : Cube q => weight s ∈ K).card := by
          congr 1
          ext s
          simp [A,layerFamily]
        _ = _ := by
          rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ K weight]
          simp_rw [layer_size]
    have inv := (symmetric_spaces (rowSpace C)).mpr ⟨K,hK,hw⟩
    refine ⟨_,hc.trans_le hb,C,?_,inv.1,inv.2,(matrix_iff_edges a C A hw).mpr
      ((layers_iff_gaps hi hn K).mpr hgap)⟩
    intro i j
    rcases walsh_sign (e.symm i).val j with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

def maxGap (q : ℕ) (K : Finset ℕ) : ℕ :=
  (Finset.range (q+1)).sup fun U => (Finset.range (U+1)).sup fun L =>
    if Disjoint (Finset.Icc L U) K then U-L else 0

theorem maxGap_le_iff (q d : ℕ) (K : Finset ℕ) : maxGap q K ≤ d ↔ gapsAtMost q d K := by
  simp only [maxGap, Finset.sup_le_iff, Finset.mem_range]
  constructor
  · intro h L U hL hU clear
    have hd : Disjoint (Finset.Icc L U) K :=
      Finset.disjoint_left.mpr fun j hj => clear j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
    simpa [hd] using h U (by omega) L (by omega)
  · intro h U hu L hl
    split
    next hd =>
      exact h L U (by omega) (by omega) fun j a b => Finset.disjoint_left.mp hd (Finset.mem_Icc.mpr ⟨a,b⟩)
    next => omega

def affordableGaps (q b : ℕ) : Set ℕ :=
  {g | ∃ K : Finset ℕ, K ⊆ Finset.range (q+1) ∧ (∑ k ∈ K, q.choose k) ≤ b ∧ g = maxGap q K}

theorem symmetric_exact_integer_budget (q b : ℕ) :
    sInf {d | symmetricScheme q b d (fun i => ((i.val+1:ℕ):ℚ))} = sInf (affordableGaps q b) := by
  let a : Fin q → ℚ := fun i => ((i.val+1:ℕ):ℚ)
  have hi : Function.Injective a := by
    intro i j hij
    apply Fin.ext
    change ((i.val+1:ℕ):ℚ) = ((j.val+1:ℕ):ℚ) at hij
    exact Nat.add_right_cancel (by exact_mod_cast hij : i.val+1=j.val+1)
  have hn (i : Fin q) : a i ≠ 0 := by dsimp [a]; positivity
  have nonemptyG : (affordableGaps q b).Nonempty :=
    ⟨maxGap q ∅,∅,Finset.empty_subset _,by simp,rfl⟩
  have go (d : ℕ) : symmetricScheme q b d a ↔ ∃ g ∈ affordableGaps q b, g ≤ d := by
    rw [symmetric_budget_iff hi hn]
    constructor
    · rintro ⟨K,hK,hb,hg⟩
      exact ⟨_,⟨K,hK,hb,rfl⟩,(maxGap_le_iff _ _ _).mpr hg⟩
    · rintro ⟨_,⟨K,hK,hb,rfl⟩,hg⟩
      exact ⟨K,hK,hb,(maxGap_le_iff _ _ _).mp hg⟩
  change sInf {d | symmetricScheme q b d a} = _
  have good := (go _).mpr ⟨_,Nat.sInf_mem nonemptyG,le_rfl⟩
  have he : Set.Nonempty {d | symmetricScheme q b d a} := ⟨_,good⟩
  obtain ⟨g,hg,hle⟩ := (go _).mp (Nat.sInf_mem he)
  exact le_antisymm (Nat.sInf_le good) ((Nat.sInf_le hg).trans hle)

end
end LocalReconstruction
