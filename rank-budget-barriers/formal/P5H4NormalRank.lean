import P5H4DetDiv

/-! One rectangular chart binds the actual quotient image and every
determinantal divisor. The value is the minimum sum of s true local
orders, not the order of an arbitrarily selected s-by-s minor. -/
namespace P5H4
open Polynomial Matrix
open scoped BigOperators Classical

variable {K m n : Type*} [Field K]

theorem multiplicity_finset_product {I : Type*} (s : Finset I) {f : K[X]}
    (hprime : Prime f) (hpos : 0 < f.natDegree) (a : I → K[X])
    (ha : ∀ i ∈ s, a i ≠ 0) :
    multiplicity f (∏ i ∈ s, a i) = ∑ i ∈ s, multiplicity f (a i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h₀ : emultiplicity f 1 = 0 := (emultiplicity_eq_coe (n:=0)).mpr
      ⟨by simp, by simpa only [Nat.zero_add,pow_one] using (show ¬f ∣ (1:K[X]) from fun h => hprime.not_unit (isUnit_iff_dvd_one.mpr h))⟩
    simpa using multiplicity_eq_of_emultiplicity_eq_some h₀
  | @insert i s hi ih =>
    have h₁ := ha i (Finset.mem_insert_self i s)
    have h₂ : ∀ j ∈ s, a j ≠ 0 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hp := polynomial_finiteMultiplicity hpos
      (mul_ne_zero h₁ (Finset.prod_ne_zero_iff.mpr h₂))
    rw [Finset.prod_insert hi,multiplicity_mul hprime hp,Finset.sum_insert hi,ih h₂]

private theorem irreducible_positive (f : K[X]) (hm : f.Monic)
    (hi : Irreducible f) : 0 < f.natDegree := by
  by_contra! h
  exact hi.not_isUnit (by
    rw [hm.natDegree_eq_zero.mp (Nat.eq_zero_of_le_zero h)]
    exact isUnit_one)

theorem normal_minor_support (A : Matrix m n K[X]) {r : ℕ} (a : Fin r → K[X])
    (ha : ∀ i, a i ≠ 0) (s : ℕ)
    (hd : ∀ d : K[X], d ∣ determinantalGCD A s ↔
      ∀ u : Fin s → Fin r, Function.Injective u → d ∣ ∏ i, a (u i)) :
    determinantalGCD A s ≠ 0 ↔ s ≤ r := by
  constructor
  · intro hn
    by_contra! hs
    have hh : (0 : K[X]) ∣ determinantalGCD A s := (hd 0).mpr (fun u hu => by
      have hk : s ≤ r := by simpa using Fintype.card_le_of_injective u hu
      omega)
    exact hn (zero_dvd_iff.mp hh)
  · intro hs hn
    have hh := (hd 0).mp (zero_dvd_iff.mpr hn)
    have hprod := zero_dvd_iff.mp (hh (Fin.castLE hs) (Fin.castLE_injective hs))
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => ha (Fin.castLE hs i)) hprod

/-- Valuations of normalized determinantal gcds are the least sums of
orders among all s distinct channels. Both attainment and lower bound
are explicit. -/
theorem normal_minor_minimum (A : Matrix m n K[X]) {r s : ℕ} (a : Fin r → K[X])
    (ha : ∀ i, a i ≠ 0) (hs : s ≤ r)
    (hd : ∀ d : K[X], d ∣ determinantalGCD A s ↔
      ∀ u : Fin s → Fin r, Function.Injective u → d ∣ ∏ i, a (u i))
    (f : K[X]) (hm : f.Monic) (hi : Irreducible f) :
    let v := multiplicity f (determinantalGCD A s)
    (∀ u : Fin s → Fin r, Function.Injective u → v ≤ ∑ i, multiplicity f (a (u i))) ∧
      ∃ u : Fin s → Fin r, Function.Injective u ∧ v = ∑ i, multiplicity f (a (u i)) := by
  let G := determinantalGCD A s
  let v := multiplicity f G
  have hG : G ≠ 0 := (normal_minor_support A a ha s hd).mpr hs
  have hpos := irreducible_positive f hm hi
  have hf (u : Fin s → Fin r) : (∏ i, a (u i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => ha (u i))
  have htest (k : ℕ) : k ≤ v ↔ ∀ u : Fin s → Fin r, Function.Injective u →
      k ≤ ∑ i, multiplicity f (a (u i)) := by
    calc
      _ ↔ f^k ∣ G :=
        (polynomial_finiteMultiplicity hpos hG).pow_dvd_iff_le_multiplicity.symm
      _ ↔ ∀ u : Fin s → Fin r, Function.Injective u → f^k ∣ ∏ i, a (u i) := hd _
      _ ↔ _ := by
        have h (u : Fin s → Fin r) :
            f^k ∣ ∏ i, a (u i) ↔ k ≤ ∑ i, multiplicity f (a (u i)) := by
          rw [(polynomial_finiteMultiplicity hpos (hf u)).pow_dvd_iff_le_multiplicity,
            multiplicity_finset_product Finset.univ hi.prime hpos (fun i => a (u i)) (fun i _ => ha (u i))]
        simp only [h]
  change (∀ u : Fin s → Fin r, Function.Injective u → v ≤ ∑ i, multiplicity f (a (u i))) ∧ _
  have hle := (htest v).mp le_rfl
  refine ⟨hle,?_⟩
  have hex : ¬∀ u : Fin s → Fin r, Function.Injective u →
      v+1 ≤ ∑ i, multiplicity f (a (u i)) := fun hh => Nat.not_succ_le_self v ((htest _).mpr hh)
  push_neg at hex
  obtain ⟨u,hu,hl⟩ := hex
  exact ⟨u,hu, le_antisymm (hle u hu) (Nat.le_of_lt_succ hl)⟩

theorem detdiv_entry_grade (A : Matrix m n K[X]) (s d : ℕ)
    (hn : determinantalGCD A s ≠ 0) (hgrade : ∀ i j, (A i j).natDegree ≤ d) :
    (determinantalGCD A s).natDegree ≤ s*d := by
  have hG := (dvd_determinantalGCD_iff A s (determinantalGCD A s)).mp (dvd_refl _)
  have he : ∃ (u : Fin s → m) (v : Fin s → n), (A.submatrix u v).det ≠ 0 := by
    by_contra! h
    exact hn (zero_dvd_iff.mp ((dvd_determinantalGCD_iff A s 0).mpr fun u v =>
      zero_dvd_iff.mpr (h u v)))
  obtain ⟨u,v,huv⟩ := he
  exact (Polynomial.natDegree_le_of_dvd (hG u v) huv).trans
    (by simpa using det_grade_bound (A.submatrix u v) d (fun i j => hgrade (u i) (v j)))

variable [Fintype m] [Fintype n]

set_option maxHeartbeats 6500000 in
theorem normal_rank_same_chart (A : Matrix m n K[X]) :
    ∃ (r : ℕ) (a : Fin r → K[X]), (∀ i, a i ≠ 0) ∧
      (∀ (f : K[X]), f.Monic → Irreducible f → ∀ k,
        quotientLength A (f^k) = ∑ i, f.natDegree*(k-min k (multiplicity f (a i)))) ∧
      (∀ s, determinantalGCD A s ≠ 0 ↔ s ≤ r) ∧
      ∀ s, s ≤ r → ∀ (f : K[X]), f.Monic → Irreducible f →
        let v := multiplicity f (determinantalGCD A s)
        (∀ u : Fin s → Fin r, Function.Injective u → v ≤ ∑ i, multiplicity f (a (u i))) ∧
          ∃ u : Fin s → Fin r, Function.Injective u ∧ v = ∑ i, multiplicity f (a (u i)) := by
  obtain ⟨r,e,a,U,Z,C,T,ha,hU,hu,hC,hT⟩ := rectangular_chart A
  have hm := chart_minors_of A e a U Z C T hU hu hC hT
  refine ⟨r,a,ha,?_,fun s => normal_minor_support A a ha s (hm s),?_⟩
  · intro f hm hf k
    have hq : (f^k).Monic := hm.pow k
    have hAZ : quotientLength A (f^k) = quotientLength Z (f^k) := by
      refine le_antisymm ?_ ?_
      · rw [← hC]
        exact (quotientLength_mul_le Z C _ hq).1
      · rw [← hT]
        exact (quotientLength_mul_le A T _ hq).1
    have hUZ := quotientLength_unimodular Z U (1:Matrix (Fin r) (Fin r) K[X])
      hU isUnit_one (f^k) hq
    rw [Matrix.mul_one,hu] at hUZ
    rw [hAZ,←hUZ,rowDiagonal_image e a _ hq,irreducible_diagonal_length f hm hf a ha k]
  · intro s hs f hmon hirr
    exact normal_minor_minimum A a ha hs (hm s) f hmon hirr

#print axioms multiplicity_finset_product
#print axioms normal_minor_support
#print axioms normal_minor_minimum
#print axioms detdiv_entry_grade
#print axioms normal_rank_same_chart
end P5H4
