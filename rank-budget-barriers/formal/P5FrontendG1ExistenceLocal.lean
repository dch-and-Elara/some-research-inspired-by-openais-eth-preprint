import P5FrontendG1TannerCertificate
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Finite, exact union-bound proof of the existence of the printed local
matrix. For each nonzero fixed word the matrix has a product decomposition,
so the fraction annihilating that word is exactly 2^(-c). No random search
is assumed as an oracle, and no running time is claimed. -/
namespace Paper5.FrontendG1.Tanner
open scoped BigOperators

def liftColumn {c d : ℕ} (j : Fin d) (y : Fin c→F₂) : Matrix (Fin c) (Fin d) F₂ :=
  fun i k => y i*singlePort j k

theorem lifted_column_mulVec {c d : ℕ} (j : Fin d) (x : Fin d→F₂)
    (hj : x j=1) (y : Fin c→F₂) : (liftColumn j y).mulVec x=y := by
  funext i
  change (∑ k, (y i*singlePort j k)*x k)=y i
  simp [singlePort,mul_ite,ite_mul,hj]

def pivotDecompose {c d : ℕ} (x : Fin d→F₂) (j : Fin d) (hj : x j=1) :
    Matrix (Fin c) (Fin d) F₂ ≃
      {A : Matrix (Fin c) (Fin d) F₂ // A.mulVec x=0} × (Fin c→F₂) where
  toFun A := (⟨A-liftColumn j (A.mulVec x),by
    rw [Matrix.sub_mulVec,lifted_column_mulVec j x hj,sub_self]⟩,A.mulVec x)
  invFun p := p.1.val + liftColumn j p.2
  left_inv A := sub_add_cancel _ _
  right_inv := by
    rintro ⟨⟨A,hA⟩,y⟩
    have hY : (A+liftColumn j y).mulVec x=y := by
      rw [Matrix.add_mulVec,lifted_column_mulVec j x hj,hA,zero_add]
    refine Prod.ext (Subtype.ext ?_) hY
    change A + liftColumn j y - liftColumn j ((A+liftColumn j y).mulVec x)=A
    rw [hY,add_sub_cancel_right]

def annihilators (c : ℕ) {d : ℕ} (x : Fin d→F₂) : Finset (Matrix (Fin c) (Fin d) F₂) :=
  Finset.univ.filter fun A=>A.mulVec x=0

theorem annihilator_fraction_exact (c : ℕ) {d : ℕ} (x : Fin d→F₂) (hx : x≠0) :
    (annihilators c x).card * 2^c = Fintype.card (Matrix (Fin c) (Fin d) F₂) := by
  classical
  have hNZ : ∃ j, x j≠0 := by
    by_contra! h
    apply hx
    funext j
    exact h j
  obtain ⟨j,hJ⟩ := hNZ
  have hj : x j=1 := (binary_cases _).resolve_left hJ
  let e : ↥(annihilators c x) ≃ {A : Matrix (Fin c) (Fin d) F₂ // A.mulVec x=0} :=
    Equiv.subtypeEquivRight (by simp [annihilators])
  have hCard := Fintype.card_congr (pivotDecompose (c:=c) x j hj)
  rw [Fintype.card_prod,←Fintype.card_congr e,Fintype.card_coe] at hCard
  simpa [F₂] using hCard.symm

def lightWords (d : ℕ) (D : ℚ) : Finset (Fin d→F₂) :=
  Finset.univ.filter fun x=>x≠0 ∧ (weight x:ℚ)<D

theorem local_exists_if_light_card (c d : ℕ) (D : ℚ) (hFew : (lightWords d D).card<2^c) :
    ∃ A : Matrix (Fin c) (Fin d) F₂, LocalDistance A D := by
  classical
  let U := (lightWords d D).biUnion (annihilators c)
  let Q := Fintype.card (Matrix (Fin c) (Fin d) F₂)
  have hQ : 0<Q := Fintype.card_pos
  have hSub : U.card≤∑ x∈lightWords d D,(annihilators c x).card := Finset.card_biUnion_le
  have hMulSmall : U.card*2^c<Q*2^c := by
    calc
      _ ≤ (∑ x∈lightWords d D,(annihilators c x).card)*2^c :=
        Nat.mul_le_mul_right _ hSub
      _ = (lightWords d D).card*Q := by
        rw [Finset.sum_mul]
        have hC (x : Fin d→F₂) (hx : x∈lightWords d D) :
            (annihilators c x).card*2^c=Q :=
          annihilator_fraction_exact c x (Finset.mem_filter.mp hx).2.1
        simp [Finset.sum_congr rfl hC]
      _ < (2^c)*Q := Nat.mul_lt_mul_of_pos_right hFew hQ
      _ = Q*2^c := Nat.mul_comm _ _
  have hSmall : U.card<Q := Nat.lt_of_mul_lt_mul_right hMulSmall
  have hExists : ∃ A : Matrix (Fin c) (Fin d) F₂,A∉U := by
    by_contra! h
    have hAll : (Finset.univ : Finset (Matrix (Fin c) (Fin d) F₂))⊆U := fun A _=>h A
    have hCard := Finset.card_le_card hAll
    rw [Finset.card_univ] at hCard
    exact (not_le_of_gt hSmall) hCard
  obtain ⟨A,hA⟩ := hExists
  refine ⟨A,?_⟩
  intro x hx hz
  by_contra! hd
  have hw : x∈lightWords d D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,hd⟩
  have hAx : A∈annihilators c x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
  exact hA (Finset.mem_biUnion.mpr ⟨x,hw,hAx⟩)

theorem word_support_injective {d : ℕ} : Function.Injective (support (W:=Fin d)) := by
  intro x y hy
  funext j
  have hj : x j≠0 ↔ y j≠0 := by
    simpa [support] using (show j∈support x ↔ j∈support y by rw [hy])
  rcases binary_cases (x j) with hx|hx <;> rcases binary_cases (y j) with hg|hg
    <;> simp_all

theorem light_card_by_bounded_weight {d : ℕ} (D : ℚ) (h : ℕ)
    (hW : ∀ x∈lightWords d D,weight x≤h) :
    (lightWords d D).card ≤ ∑ k∈Finset.range (h+1),d.choose k := by
  let T := (Finset.range (h+1)).biUnion fun k=>(Finset.univ : Finset (Fin d)).powersetCard k
  have hSub : Set.MapsTo (support (W:=Fin d)) (lightWords d D : Set _) (T : Set _) := by
    intro x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨weight x,Finset.mem_range.mpr (Nat.lt_succ_of_le (hW x hx)),?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,rfl⟩
  calc
    _ ≤ T.card := Finset.card_le_card_of_injOn _ hSub word_support_injective.injOn
    _ ≤ ∑ k∈Finset.range (h+1),((Finset.univ : Finset (Fin d)).powersetCard k).card :=
      Finset.card_biUnion_le
    _ = _ := by simp [Finset.card_powersetCard]

theorem source_light_words_lt {B m : ℕ} (hB : 0<B) (hm : 0<m) :
    (lightWords (sourceDegree B m) (sourceMinDistance B m)).card < 2^(sourceLocalRows B m) := by
  let d := sourceDegree B m
  let c := sourceLocalRows B m
  let u := sourceMu m
  let t := 100*B*u
  let h := (d-1)/t
  have hd : 0<d := source_d_pos hB hm
  have hu : 1≤u := by change 1≤Nat.log 2 m+1; omega
  have ht : 0<t := by positivity
  have htQ : (0:ℚ)<t := by exact_mod_cast ht
  have hMinD : sourceMinDistance B m = (d:ℚ)/(t:ℚ) := by
    rw [sourceMinDistance,sourceDelta,one_div_mul_eq_div]
    simp [d,t,u]
  have hSup (x : Fin d→F₂) (hx : x∈lightWords d (sourceMinDistance B m)) :
      weight x≤h := by
    have hLt := (Finset.mem_filter.mp hx).2.2
    rw [hMinD,lt_div_iff₀ htQ] at hLt
    have hNat : weight x*t<d := by exact_mod_cast hLt
    apply (Nat.le_div_iff_mul_le ht).mpr
    omega
  have htBound : h*t<d := by
    have hh : h*t≤d-1 := Nat.div_mul_le_self _ _
    omega
  have hdc : d≤c*(8*B) := (ceilNat_le_iff d (8*B) c (by positivity)).mp le_rfl
  have huCot : 8*(1+u)≤100*u := by omega
  have hk : h*(1+u)<c := by
    have hmul : (8*B)*(h*(1+u))≤h*t := by
      calc
        _ = (B*h)*(8*(1+u)) := by ring
        _ ≤ (B*h)*(100*u) := Nat.mul_le_mul_left _ huCot
        _ = _ := by dsimp [t]; ring
    have hs : (8*B)*(h*(1+u))<(8*B)*c :=
      (hmul.trans_lt (htBound.trans_le hdc)).trans_eq (Nat.mul_comm _ _)
    exact Nat.lt_of_mul_lt_mul_left hs
  have hD2 : d≤2^u := (Nat.min_le_left _ _).trans
    (Nat.lt_pow_succ_log_self (by decide : 1<(2:ℕ)) m).le
  have hlen : ∀ j : ℕ,j+1≤2^j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih => rw [pow_succ']; omega
  calc
    _ ≤ ∑ k∈Finset.range (h+1),d.choose k := light_card_by_bounded_weight _ h hSup
    _ ≤ ∑ _k∈Finset.range (h+1),d^h := by
      apply Finset.sum_le_sum
      intro k hk'
      exact (Nat.choose_le_pow d k).trans
        (Nat.pow_le_pow_right hd (Nat.le_of_lt_succ (Finset.mem_range.mp hk')))
    _ = (h+1)*d^h := by simp
    _ ≤ 2^h*(2^u)^h := Nat.mul_le_mul (hlen h)
        (Nat.pow_le_pow_left hD2 h)
    _ = 2^(h*(1+u)) := by
      rw [←mul_pow,←pow_succ',←pow_mul]
      congr 1
      ring
    _ < 2^c := Nat.pow_lt_pow_right (by decide) hk

theorem source_local_matrix_exists {B m : ℕ} (hB : 0<B) (hm : 0<m) :
    ∃ A : Matrix (Fin (sourceLocalRows B m)) (Fin (sourceDegree B m)) F₂,
      localViolations A (sourceMinDistance B m)=∅ := by
  obtain ⟨A,hA⟩ := local_exists_if_light_card _ _ _ (source_light_words_lt hB hm)
  exact ⟨A,(localViolations_empty_exact A _).mpr hA⟩

#print axioms lifted_column_mulVec
#print axioms annihilator_fraction_exact
#print axioms local_exists_if_light_card
#print axioms word_support_injective
#print axioms light_card_by_bounded_weight
#print axioms source_light_words_lt
#print axioms source_local_matrix_exists
end Paper5.FrontendG1.Tanner