import P3WalshGeometry

open scoped Polynomial BigOperators
open Polynomial

namespace Paper3.WalshAssembly

open AffineEdge AffineEdge.Orbit
open Reconstruction.ReleaseColor.Walsh

noncomputable section

def keptUpper {q : ℕ} (u : Word q) : ℕ :=
  if Fintype.card (Active u) = q then q-1 else Fintype.card (Active u)

/-- Measure no rows on the small orbits, the constant on each one-inactive
orbit, and the constant and actual full Walsh character on the all-active orbit. -/
def printedC (q : ℕ) : Matrix (BoundaryRow q) (Word q) ℚ
  | .inl p, v => if key v = nearKey p then 1 else 0
  | .inr false, v => if key v = fullKey q then 1 else 0
  | .inr true, v =>
      if key v = fullKey q then character (Finset.univ : Finset (Fin q)) v.1 else 0

/-- The blockwise polynomial in the printed attainment proof: a diagonal
gate on small orbits and the local Walsh polynomial on the exact larger cube. -/
def printedP {q : ℕ} (sites : Fin q → ℚ) (u v : Word q) : ℚ[X] :=
  if key v = key u then
    if Fintype.card (Active u) ≤ q-2 then
      if u = v then diagonalGate sites (activeSet u) else 0
    else
      walshMatrix (fun t : Active u => sites t.val) 1 (keptUpper u)
        (orientation u u) (orientation u v)
  else 0

theorem printedC_orbitwise (q : ℕ) : Orbitwise (printedC q) := by
  apply orbitwise_of_supported_rows
  intro j
  cases j with
  | inl p => exact ⟨nearKey p, fun v h => by simp [printedC,h]⟩
  | inr b =>
    refine ⟨fullKey q, ?_⟩
    cases b <;> intro v h <;> simp [printedC,h]

theorem keptUpper_degree {q : ℕ} {u : Word q} (hq : 2 ≤ q)
    (hl : ¬ Fintype.card (Active u) ≤ q-2) : keptUpper u - 1 ≤ q-2 := by
  have h := active_card_le u
  unfold keptUpper
  split <;> omega

theorem printedP_degree {q : ℕ} (sites : Fin q → ℚ) (hq : 2 ≤ q)
    (hn : ∀ t, sites t ≠ 0) (u v : Word q) : (printedP sites u v).natDegree ≤ q-2 := by
  by_cases hk : key v = key u
  · by_cases hl : Fintype.card (Active u) ≤ q-2
    · by_cases huv : u = v
      · have h := (diagonalGate_properties sites (activeSet u) (fun t _ => hn t)).1
        rw [printedP,if_pos hk,if_pos hl,if_pos huv]
        exact h.trans (by simpa only [← active_card] using hl)
      · simp only [printedP,if_pos hk,if_pos hl,if_neg huv,natDegree_zero,Nat.zero_le]
    · rw [printedP,if_pos hk,if_neg hl]
      exact (walshMatrix_degree (fun t : Active u => sites t.val) 1 (keptUpper u)
        (orientation u u) (orientation u v)).trans (keptUpper_degree hq hl)
  · simp [printedP,hk]

theorem printedP_origin {q : ℕ} (sites : Fin q → ℚ)
    (hn : ∀ t, sites t ≠ 0) (u v : Word q) :
    (printedP sites u v).eval 0 = if u = v then 1 else 0 := by
  classical
  by_cases hk : key v = key u
  · by_cases hl : Fintype.card (Active u) ≤ q-2
    · by_cases huv : u = v
      · simpa only [printedP,if_pos hk,if_pos hl,if_pos huv] using
          (diagonalGate_properties sites (activeSet u) (fun t _ => hn t)).2.1
      · simp only [printedP,if_pos hk,if_pos hl,if_neg huv,eval_zero]
    · have he : orientation u u = orientation u v ↔ u = v :=
        ⟨fun h => by
          calc
            u = inflate u (orientation u u) := (inflate_orientation rfl).symm
            _ = inflate u (orientation u v) := congrArg (inflate u) h
            _ = v := inflate_orientation hk, fun h => by subst v; rfl⟩
      simp only [printedP,hk,hl,if_true,if_false,walshMatrix_zero,he]
  · have huv : u ≠ v := fun h => hk (congrArg key h.symm)
    simp [printedP,hk,huv]

theorem literal_bands {q : ℕ} {u : Word q} (hq : 2 ≤ q)
    (S : Finset (Active u))
    (hs : S.card ∉ Finset.Icc 1 (keptUpper u)) :
    S = ∅ ∨ Fintype.card (Active u) = q ∧ S = Finset.univ := by
  have hc := active_card_le u
  have hsle : S.card ≤ Fintype.card (Active u) := Finset.card_le_univ S
  by_cases hf : Fintype.card (Active u) = q
  · simp only [keptUpper, hf, if_true, Finset.mem_Icc] at hs
    by_cases hz : S.card = 0
    · exact Or.inl (Finset.card_eq_zero.mp hz)
    · exact Or.inr ⟨hf, Finset.eq_univ_of_card S (by omega)⟩
  · simp only [keptUpper, hf, if_false, Finset.mem_Icc] at hs
    exact Or.inl (Finset.card_eq_zero.mp (by omega))

theorem literal_constant_coefficient {q : ℕ} {u : Word q} (hq : 2 ≤ q)
    (hl : ¬ Fintype.card (Active u) ≤ q-2) (z : Word q → ℚ)
    (zk : ∀ j, ∑ v, printedC q j v * z v = 0) :
    coefficient (∅ : Finset (Active u)) (fun x => z (inflate u x)) = 0 := by
  classical
  have hc := active_card_le u
  simp only [coefficient, character, Finset.prod_empty, mul_one, sum_fibre]
  by_cases hf : Fintype.card (Active u) = q
  · simpa only [printedC, full_key_of_card hf, ite_mul, one_mul, zero_mul] using zk (.inr false)
  · have hh : Fintype.card (Active u) = q-1 := by omega
    obtain ⟨p,hp⟩ := near_key_of_card hq hh
    simpa only [printedC, hp, ite_mul, one_mul, zero_mul] using zk (.inl p)

theorem literal_full_coefficient {q : ℕ} {u : Word q}
    (hf : Fintype.card (Active u) = q) (z : Word q → ℚ)
    (zk : ∀ j, ∑ v, printedC q j v * z v = 0) :
    coefficient (Finset.univ : Finset (Active u)) (fun x => z (inflate u x)) = 0 := by
  classical
  have hw (x : Active u → Bool) :
      character (Finset.univ : Finset (Active u)) x =
        character (Finset.univ : Finset (Fin q)) (inflate u x).1 := by
    rw [← full_character u (inflate u x) hf, orientation_inflate]
  simp only [coefficient,hw]
  rw [sum_fibre u (fun v => z v * character (Finset.univ : Finset (Fin q)) v.1)]
  rw [full_key_of_card hf]
  have h := zk (.inr true)
  simp only [printedC] at h
  calc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hk : key v = fullKey q <;> simp [hk,mul_comm]
    _ = 0 := h

theorem large_sum_eq {q : ℕ} {u : Word q} (hl : ¬ Fintype.card (Active u) ≤ q-2)
    (sites : Fin q → ℚ) (t : Fin q) (z : Word q → ℚ) :
    (∑ v, (printedP sites u v).eval (sites t) * z v) =
      ∑ x : Active u → Bool,
        (walshMatrix (fun i : Active u => sites i.val) 1 (keptUpper u) (orientation u u) x).eval
          (sites t) * z (inflate u x) := by
  classical
  let f (v : Word q) := (walshMatrix (fun i : Active u => sites i.val) 1 (keptUpper u)
      (orientation u u) (orientation u v)).eval (sites t) * z v
  calc
    _ = ∑ v : Word q, if key v = key u then f v else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hk : key v = key u
      · simp only [printedP,if_pos hk,if_neg hl,f]
      · simp only [printedP,if_neg hk,eval_zero,zero_mul]
    _ = ∑ x : Active u → Bool, f (inflate u x) := (sum_fibre u f).symm
    _ = _ := by simp [f]

theorem printedP_local {q : ℕ} (sites : Fin q → ℚ) (hq : 2 ≤ q)
    (hn : ∀ t, sites t ≠ 0) (u : Word q) (t : Fin q) (z : Word q → ℚ)
    (zk : ∀ j, ∑ v, printedC q j v * z v = 0)
    (zl : ∀ v, v.1 t = u.2 t → z v = 0) :
    ∑ v, (printedP sites u v).eval (sites t) * z v = 0 := by
  classical
  by_cases hl : Fintype.card (Active u) ≤ q-2
  · rw [Finset.sum_eq_single u]
    · by_cases ht : u.1 t ≠ u.2 t
      · have hm : t ∈ activeSet u := by simp [activeSet,ht]
        have hg := (diagonalGate_properties sites (activeSet u) (fun s _ => hn s)).2.2 t hm
        simp only [printedP,if_true,if_pos hl,hg,zero_mul]
      · simp [zl u (not_not.mp ht)]
    · intro v _ hv
      by_cases hk : key v = key u
      · simp only [printedP,if_pos hk,if_pos hl,if_neg (Ne.symm hv),eval_zero,zero_mul]
      · simp only [printedP,if_neg hk,eval_zero,zero_mul]
    · exact fun h => (h (Finset.mem_univ u)).elim
  · by_cases ht : u.1 t ≠ u.2 t
    · let i : Active u := ⟨t,ht⟩
      rw [large_sum_eq hl sites t z]
      refine walshMatrix_local (fun j : Active u => sites j.val) 1 (keptUpper u)
        (orientation u u) i (hn t) (fun x => z (inflate u x)) ?_ ?_
      · intro x hx
        apply zl (inflate u x)
        apply (active_known u (inflate u x) i).mpr
        simpa only [orientation_inflate] using hx
      · intro S hs
        rcases literal_bands hq S hs with e | ⟨hf,e⟩
        · rw [e]
          exact literal_constant_coefficient hq hl z zk
        · rw [e]
          exact literal_full_coefficient hf z zk
    · apply Finset.sum_eq_zero
      intro v _
      by_cases hk : key v = key u
      · exact mul_eq_zero_of_right _ (zl v ((inactive_same hk (not_not.mp ht)).1.trans (not_not.mp ht)))
      · simp [printedP,hk]

theorem original_Walsh_recovers {q : ℕ} (sites : Fin q → ℚ) (hq : 2 ≤ q)
    (hn : ∀ t, sites t ≠ 0) :
    PairedCondition sites (printedC q) (q-2) (printedP sites) :=
  ⟨printedP_degree sites hq hn, printedP_origin sites hn, printedP_local sites hq hn⟩

/-- Proposition 5's boundary attainment by the original physical Walsh
matrix itself. Only the published distinct, nonzero site guards are used. -/
theorem original_Walsh_attains {q : ℕ} (sites : Fin q → ℚ) (hq : 2 ≤ q)
    (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0) :
    Orbitwise (printedC q) ∧ PairedCondition sites (printedC q) (q-2) (printedP sites) ∧
      (printedC q).rank = 2*q+2 := by
  have ho := printedC_orbitwise q
  have hp := original_Walsh_recovers sites hq hn
  refine ⟨ho,hp,le_antisymm ?_ (orbitwise_boundary_rank_lower hq hi ho hp)⟩
  simpa [BoundaryRow,Nat.mul_comm] using (printedC q).rank_le_card_height

end

end Paper3.WalshAssembly

#print axioms Paper3.WalshAssembly.printedC_orbitwise
#print axioms Paper3.WalshAssembly.printedP_degree
#print axioms Paper3.WalshAssembly.printedP_origin
#print axioms Paper3.WalshAssembly.literal_constant_coefficient
#print axioms Paper3.WalshAssembly.literal_full_coefficient
#print axioms Paper3.WalshAssembly.printedP_local
#print axioms Paper3.WalshAssembly.original_Walsh_recovers
#print axioms Paper3.WalshAssembly.original_Walsh_attains

