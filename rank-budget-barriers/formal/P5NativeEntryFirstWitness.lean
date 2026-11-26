import P5NativeEntryBranch

/-! The separate first-round witness from the final paragraph of the
source audit. Even without any conclusion about the eventual chosen
row, its ordered singleton list is one of the paid candidate calls. -/
namespace Paper5.NativeEntry
open scoped BigOperators

private theorem degree_countP {n : ℕ} (A : Rows n) (v : Fin n) :
    degree A v=1+A.countP (fun r=> !(decide (r v=0))) := by
  induction A with
  | nil => simp [degree]
  | cons r A ih =>
    rw [degree,Finset.card_filter]
    simp only [List.length_cons,Fin.sum_univ_succ,List.get_cons_zero]
    rw [degree,Finset.card_filter] at ih
    simp only [List.countP_cons]
    by_cases h : r v=0 <;> simp [h] at ih ⊢ <;> omega

theorem degree_appended {n : ℕ} (A : Rows n) (r : Word n) (v : Fin n) :
    degree (A++[r]) v=degree A v+(if r v≠0 then 1 else 0) := by
  rw [degree_countP,degree_countP,List.countP_append]
  by_cases h : r v=0 <;> simp [h,Nat.add_assoc]

theorem singleton_incidence_increase {n : ℕ} (A : Rows n) (v : Fin n) :
    incidences (A++[singletonRow v])=incidences A+1 := by
  unfold incidences
  simp only [degree_appended,Finset.sum_add_distrib]
  congr 1
  have h (w : Fin n) : (if singletonRow v w≠0 then 1 else 0) =
      (if w=v then 1 else 0) := by
    by_cases hv : w=v
    · subst w; simp [singletonRow]
    · simp [singletonRow,hv,Ne.symm hv]
  simp [h]

theorem minimal_incidence_exists {n : ℕ} (A : Rows n) (hn : 0<n) :
    ∃ v : Fin n,n*degree A v≤ incidences A := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨v,_,h⟩ := Finset.exists_min_image Finset.univ (degree A) Finset.univ_nonempty
  refine ⟨v,?_⟩
  unfold incidences
  calc
    _ = ∑ _w : Fin n,degree A v := by simp
    _ ≤ _ := Finset.sum_le_sum h

theorem first_singleton_survives {n : ℕ} (A : Rows n) (hn : 20≤n) :
    ∃ v : Fin n,v∈(fixed (A++[singletonRow v]))ᶜ := by
  obtain ⟨v,hv⟩ := minimal_incidence_exists A (by omega)
  refine ⟨v,?_⟩
  let C := A++[singletonRow v]
  have hc : degree C v=degree A v+1 := by simp [C,degree_appended,singletonRow]
  have hm : incidences C=incidences A+1 := singleton_incidence_increase A v
  have hceil := le_mul_divUp (incidences C) n (by omega)
  have hd : degree A v+1≤divUp (incidences C) n := by
    by_contra! h
    have hlow : divUp (incidences C) n≤degree A v := by omega
    have hmul := Nat.mul_le_mul_left n hlow
    omega
  have hL : 0<Nat.clog 2 n := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by simpa using hn.trans' (by decide : 2≤20))
  have hs : 1≤ceilSqrt (Nat.clog 2 n) := by
    have hp := ceilSqrt_sq_ge (Nat.clog 2 n)
    by_contra! H
    have he : ceilSqrt (Nat.clog 2 n)=0 := by omega
    simp [he] at hp
    omega
  have ht : degree C v≤fixingThreshold C := by
    rw [hc,fixingThreshold]
    calc
      _ ≤ divUp (incidences C) n := hd
      _ = divUp (incidences C) n*1 := by simp
      _ ≤ _ := Nat.mul_le_mul_left _ hs
  simpa [fixed,not_lt] using ht

theorem first_round_reaches_nonconstant {n P : ℕ} (A : Rows n) (hn : 20≤n) (hP : 0<P) :
    ∃ γ : Candidate n P, (retained (A++[candidateRow γ])).Nonempty := by
  obtain ⟨v,hv⟩ := first_singleton_survives A hn
  refine ⟨singletonList hP v,?_⟩
  rw [singleton_represented]
  let C := A++[singletonRow v]
  let i : Fin C.length := ⟨A.length,by simp [C]⟩
  refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  refine ⟨(⟨v,hv⟩ : Free C),(mem_restricted_support _ _ _).mpr ?_⟩
  have hi : C.get i=singletonRow v := by
    change (A++[singletonRow v])[A.length] = _
    rw [List.getElem_append_right le_rfl]
    simp
  rw [hi]
  simp [singletonRow]

#print axioms degree_appended
#print axioms singleton_incidence_increase
#print axioms minimal_incidence_exists
#print axioms first_singleton_survives
#print axioms first_round_reaches_nonconstant
end Paper5.NativeEntry