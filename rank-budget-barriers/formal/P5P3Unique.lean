import P5P3Canonical
import RBDeterminant

/-! The characteristic-comparison decoder is the unique degree-window
Hermite interpolation, not just some inverse on the retained data. -/
namespace Paper5.P3
open scoped BigOperators Polynomial
open Polynomial

variable {K : Type*} [Field K] {T : Type*} [Fintype T] [DecidableEq T]

theorem truncate_natDegree (n : ℕ) (p : K[X]) : (truncate n p).natDegree ≤ n-1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le _).trans (by have hi := i.isLt; omega)

theorem shift_natDegree (u : K) (p : K[X]) : (shift u p).natDegree ≤ p.natDegree := by
  change (p.comp (C u+X)).natDegree ≤ p.natDegree
  have h : (C u+X).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le ..).trans ?_
    simp
  have H := Nat.mul_le_mul_left p.natDegree h
  rw [Nat.mul_one] at H
  exact (Polynomial.natDegree_comp_le ..).trans H

theorem carrier_natDegree (u : T→K) (q : T→ℕ) (t : T) :
    (carrier u q t).natDegree ≤ ∑ s∈Finset.univ.erase t,q s := by
  unfold carrier
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply Finset.sum_le_sum
  intro s _
  apply (Polynomial.natDegree_pow_le_of_le (q s) (m:=1) ?_).trans
  · simp
  · refine (Polynomial.natDegree_mul_le ..).trans ?_
    simp only [Polynomial.natDegree_C,add_zero]
    exact Polynomial.natDegree_X_sub_C_le _

theorem fixed_interpolate_degree (O : Subring K) (u : T→K) (q : T→ℕ)
    (hS : 0 < ∑ t,q t) (hd : ∀ r s,(u r-u s)⁻¹∈O) (y : T→K[X]) :
    (fixedInterpolate O u q hd y).degree < (↑(∑ t,q t:ℕ):WithBot ℕ) := by
  let S : ℕ := ∑ t,q t
  have hs : (fixedInterpolate O u q hd y).natDegree ≤ S-1 := by
    unfold fixedInterpolate
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro t _
    by_cases hq : q t=0
    · have hzero (p : K[X]) : truncate 0 p=0 := by simp [truncate]
      rw [singleDecoder,hq,hzero,map_zero,mul_zero,natDegree_zero]
      exact Nat.zero_le _
    · unfold singleDecoder
      refine (Polynomial.natDegree_mul_le ..).trans <|
        (add_le_add (carrier_natDegree u q t) ((shift_natDegree ..).trans (truncate_natDegree ..))).trans ?_
      have ht : (∑ s∈Finset.univ.erase t,q s)+q t=S :=
        Finset.sum_erase_add (s:=Finset.univ) q (Finset.mem_univ t)
      omega
  have hs' : (fixedInterpolate O u q hd y).natDegree < S := by
    change 0 < S at hS
    omega
  exact (Polynomial.degree_le_natDegree (p:=fixedInterpolate O u q hd y)).trans_lt
    (WithBot.coe_lt_coe.mpr hs')

theorem normalized_same_jet_dvd (u : K) (q : ℕ) (f g : K[X])
    (h : AdjoinRoot.mk (X^q) (shift u f) = AdjoinRoot.mk (X^q) (shift u g)) :
    (X-C u)^q ∣ f-g := by
  have H := map_dvd (shift (-u)) (AdjoinRoot.mk_eq_mk.mp h)
  have he (p : K[X]) : shift (-u) (shift u p)=p := by
    simpa only [neg_neg] using shift_inverse (-u) p
  have hk : C (-u)+X = X-C u := by rw [map_neg,sub_eq_add_neg,add_comm]
  rwa [map_pow,shift_X,map_sub,he,he,hk] at H

omit [DecidableEq T] in
theorem multiplicity_budget_indexed (u : T→K) (q : T→ℕ) (hi : Function.Injective u)
    (p : K[X]) (hp : p≠0) (h : ∀ t,(X-C (u t))^(q t) ∣ p) :
    (∑ t,q t) ≤ p.natDegree := by
  classical
  let s := Finset.univ.image u
  let e : T ≃ s := Equiv.ofBijective (fun t => ⟨u t,Finset.mem_image.mpr ⟨t,Finset.mem_univ t,rfl⟩⟩)
    ⟨fun t a h => hi (congrArg Subtype.val h),fun z => by
      obtain ⟨t,_,ht⟩ := Finset.mem_image.mp z.property
      exact ⟨t,Subtype.ext ht⟩⟩
  let Q : K→ℕ := fun a => if ha : a∈s then q (e.symm ⟨a,ha⟩) else 0
  have hQ (t : T) : Q (u t)=q t := by
    dsimp only [Q]
    have hmem : u t ∈ s := (e t).property
    rw [dif_pos hmem]
    exact congrArg q (e.symm_apply_apply t)
  have hd (a : K) (ha : a∈s) : (X-C a)^Q a ∣ p := by
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp ha
    rw [hQ]
    exact h t
  have HB := RankBudget.multiplicityBudget p hp s Q hd
  rw [←Finset.sum_coe_sort] at HB
  exact (Fintype.sum_equiv e q (fun a : s => Q a.val) (fun t => (hQ t).symm)).trans_le HB

omit [DecidableEq T] in
theorem unique_degree_interpolation (u : T→K) (q : T→ℕ) (hi : Function.Injective u)
    (f g : K[X]) (hf : f.degree < (↑(∑ t,q t:ℕ):WithBot ℕ))
    (hg : g.degree < (↑(∑ t,q t:ℕ):WithBot ℕ))
    (he : ∀ t,AdjoinRoot.mk (X^(q t)) (shift (u t) f) = AdjoinRoot.mk (X^(q t)) (shift (u t) g)) :
    f=g := by
  by_contra hne
  have hdiff : f-g ≠ 0 := sub_ne_zero.mpr hne
  have lo := multiplicity_budget_indexed u q hi (f-g) hdiff
    (fun t => normalized_same_jet_dvd (u t) (q t) f g (he t))
  have H := (Polynomial.degree_sub_le f g).trans_lt (max_lt_iff.mpr ⟨hf,hg⟩)
  exact (not_lt_of_ge lo) ((Polynomial.natDegree_lt_iff_degree_lt hdiff).mpr H)

theorem fixed_unique_interpolant (O : Subring K) (u : T→K) (q : T→ℕ)
    (hS : 0 < ∑ t,q t) (hi : Function.Injective u) (hd : ∀ r s,(u r-u s)⁻¹∈O)
    (y : T→K[X]) :
    ∃! p : K[X], p.degree < (↑(∑ t,q t:ℕ):WithBot ℕ) ∧
      ∀ t,AdjoinRoot.mk (X^(q t)) (shift (u t) p) = AdjoinRoot.mk (X^(q t)) (y t) := by
  refine ⟨fixedInterpolate O u q hd y,⟨fixed_interpolate_degree O u q hS hd y,
    fixed_interpolate_jets O u q hi hd y⟩,?_⟩
  intro p ⟨hpd,hp⟩
  refine unique_degree_interpolation u q hi p _ hpd (fixed_interpolate_degree O u q hS hd y) ?_
  exact fun t => (hp t).trans (fixed_interpolate_jets O u q hi hd y t).symm

#print axioms fixed_interpolate_degree
#print axioms multiplicity_budget_indexed
#print axioms unique_degree_interpolation
#print axioms fixed_unique_interpolant
end Paper5.P3
