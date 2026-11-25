import AffineEdgeOrbit

open Polynomial
open scoped BigOperators Polynomial Classical

namespace AffineEdge.Orbit

noncomputable section

variable {q : ℕ} {A F I : Type*} [LinearOrder A] [Fintype A] [Field F]

def pivot (o : Key q A) : Option (Fin q) :=
  if h : ∃ t, (o t).1 ≠ (o t).2 then some (Classical.choose h) else none

omit [Fintype A] in
theorem pivot_active {o : Key q A} {t : Fin q} (h : pivot o = some t) :
    (o t).1 ≠ (o t).2 := by
  unfold pivot at h
  split at h
  next he =>
    rw [← Option.some.inj h]
    exact Classical.choose_spec he
  next => contradiction

def Representative (w : PairWord q A) : Prop :=
  ∃ t, pivot (key w) = some t ∧ w.1 t < w.2 t

abbrev Rep (q : ℕ) (A : Type*) [LinearOrder A] := {w : PairWord q A // Representative w}

omit [Fintype A] in
theorem rep_nondiag {w : PairWord q A} (h : Representative w) : w.1 ≠ w.2 := by
  obtain ⟨t, _, ht⟩ := h
  exact fun he => (ne_of_lt ht) (congrFun he t)

omit [Fintype A] in
theorem representative_swap {w : PairWord q A} (h : w.1 ≠ w.2) :
    Representative (swap w) ↔ ¬ Representative w := by
  have he : ∃ t, (key w t).1 ≠ (key w t).2 := by
    by_contra! h'
    apply h
    funext t
    exact not_ne_iff.mp (fun hn => (key_active w t).mpr hn (h' t))
  let t := Classical.choose he
  have hp : pivot (key w) = some t := by simp [pivot, he, t]
  have ht := (key_active w t).mp (Classical.choose_spec he)
  have h' : Representative w ↔ w.1 t < w.2 t := by simp [Representative, hp]
  have h'' : Representative (swap w) ↔ w.2 t < w.1 t := by
    rw [Representative, key_swap, hp]
    simp [swap]
  rw [h', h'']
  exact ⟨fun hlt => not_lt_of_gt hlt, fun hn => lt_of_le_of_ne (le_of_not_gt hn) ht.symm⟩

private def representativeEquiv (q : ℕ) (A : Type*) [LinearOrder A] :
    {w : PairWord q A // w.1 ≠ w.2} ≃ Rep q A ⊕ Rep q A where
  toFun w := if h : Representative w.val then .inl ⟨w.val,h⟩
    else .inr ⟨swap w.val,(representative_swap w.property).mpr h⟩
  invFun
    | .inl w => ⟨w.val, rep_nondiag w.property⟩
    | .inr w => ⟨swap w.val, (rep_nondiag w.property).symm⟩
  left_inv w := by
    by_cases h : Representative w.val <;> simp [h]
  right_inv w := by
    cases w with
    | inl w => simp [w.property]
    | inr w =>
      have h : ¬ Representative (swap w.val) :=
        fun he => (representative_swap (rep_nondiag w.property)).mp he w.property
      simp [h]

theorem representative_card (q r : ℕ) :
    Fintype.card (Rep q (Fin r)) = (r^(2*q)-r^q)/2 := by
  classical
  have he := Fintype.card_congr (representativeEquiv q (Fin r))
  have hd : Fintype.card {w : PairWord q (Fin r) // w.1 = w.2} = r^q := by
    let e : {w : PairWord q (Fin r) // w.1 = w.2} ≃ (Fin q → Fin r) :=
      { toFun := fun w => w.val.1
        invFun := fun a => ⟨(a,a),rfl⟩
        left_inv := fun w => Subtype.ext (Prod.ext rfl w.property)
        right_inv := fun _ => rfl }
    simpa [Fintype.card_fun] using Fintype.card_congr e
  have hN : Fintype.card {w : PairWord q (Fin r) // w.1 ≠ w.2} = r^(2*q)-r^q := by
    rw [Fintype.card_subtype_compl (fun w : PairWord q (Fin r) => w.1 = w.2), hd]
    simp [two_mul, pow_add]
  rw [hN, Fintype.card_sum] at he
  omega

theorem eval_of_degree_zero {p : F[X]} (h : p.natDegree ≤ 0) (s : F) : p.eval s = p.eval 0 := by
  rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h), eval_C, eval_C]

theorem orbitwise_zero_rank_lower [Fintype I] {sites : Fin q → F}
    {C : Matrix I (PairWord q A) F} {P : PairWord q A → PairWord q A → F[X]}
    (ho : Orbitwise C) (hp : PairedCondition sites C 0 P) :
    Fintype.card (Rep q A) ≤ C.rank := by
  apply rank_le_of_independent_columns C Subtype.val
  apply independent_physical_columns C Subtype.val Subtype.val_injective
  intro z hker hs u
  obtain ⟨t, ht, hlt⟩ := u.property
  let y := project (key u.val) z
  have hlocal (v : PairWord q A) (hv : v.1 t = u.val.2 t) : y v = 0 := by
    by_cases he : key v = key u.val
    · by_cases hr : Representative v
      · obtain ⟨s, hps, hvs⟩ := hr
        have hst : s = t := Option.some.inj (hps.symm.trans (he ▸ ht))
        subst s
        have h := congrArg (fun o : Key q A => (o t).1) he
        have hfirst : v.1 t = u.val.1 t := by
          simpa [key, min_eq_left (le_of_lt hvs), min_eq_left (le_of_lt hlt)] using h
        exact (ne_of_lt hlt (hfirst.symm.trans hv)).elim
      · simp [y, project, hs v (fun h => by obtain ⟨a,rfl⟩ := h; exact hr a.property)]
    · simp [y, project, he]
  have h := hp.2.2 u.val t y (kernel_project ho z hker _) hlocal
  simp only [eval_of_degree_zero (hp.1 _ _) (sites t), hp.2.1, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  simpa [y, project] using h

/-- One binary-valued row for each antipodal pair in a nonsingleton orbit. -/
def zeroEncoder (q : ℕ) (A : Type*) [LinearOrder A] :
    Matrix (Rep q A) (PairWord q A) F :=
  fun w v => if v = w.val ∨ v = swap w.val then 1 else 0

omit [Fintype A] in
theorem zeroEncoder_orbitwise : Orbitwise (zeroEncoder (F := F) q A) := by
  apply orbitwise_of_supported_rows
  intro j
  refine ⟨key j.val, fun v hv => ?_⟩
  simp [zeroEncoder, show v ≠ j.val from fun e => hv (congrArg key e),
    show v ≠ swap j.val from fun e => hv ((congrArg key e).trans (key_swap j.val))]

theorem zeroEncoder_attains (sites : Fin q → F) :
    ∃ P, PairedCondition sites (zeroEncoder q A) 0 P := by
  classical
  refine ⟨fun u v => if u = v then 1 else 0, ?_, ?_, ?_⟩
  · intro u v
    by_cases h : u = v <;> simp [h]
  · intro u v
    by_cases h : u = v <;> simp [h]
  · intro u t z hk hl
    suffices hu : z u = 0 by
      simpa [apply_ite, ite_mul] using hu
    by_cases hu : u.1 t = u.2 t
    · exact hl u hu
    have hne : u.1 ≠ u.2 := fun h => hu (congrFun h t)
    have hz : z (swap u) = 0 := hl (swap u) rfl
    have hsum (w : Rep q A) : z w.val + z (swap w.val) = 0 := by
      have hw : w.val ≠ swap w.val := fun he => rep_nondiag w.property (congrArg Prod.fst he)
      have hh := hk w
      simp only [zeroEncoder, ite_mul, one_mul, zero_mul] at hh
      have he (v : PairWord q A) :
          (if v = w.val ∨ v = swap w.val then z v else 0) =
          (if v = w.val then z v else 0) + (if v = swap w.val then z v else 0) := by
        by_cases h1 : v = w.val <;> by_cases h2 : v = swap w.val
        · exact (hw (h1.symm.trans h2)).elim
        · simp [h1,hw]
        · simp [h2,Ne.symm hw]
        · simp [h1,h2]
      simpa only [he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh
    by_cases hr : Representative u
    · simpa [hz] using hsum ⟨u,hr⟩
    · have h := hsum ⟨swap u,(representative_swap hne).mpr hr⟩
      simpa [hz] using h

theorem zeroEncoder_rank (q r : ℕ) (sites : Fin q → F) :
    (zeroEncoder (F := F) q (Fin r)).rank = (r^(2*q)-r^q)/2 := by
  obtain ⟨P,hP⟩ := zeroEncoder_attains (A := Fin r) sites
  rw [← representative_card]
  exact le_antisymm (zeroEncoder (F := F) q (Fin r)).rank_le_card_height
    (orbitwise_zero_rank_lower zeroEncoder_orbitwise hP)

end
end AffineEdge.Orbit
