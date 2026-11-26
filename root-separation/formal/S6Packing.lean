import S6Placement
import S6Iterators

namespace Section6

open Finset
open scoped BigOperators
set_option linter.unusedSectionVars false

variable {E U : Type*} [Fintype E] [Fintype U] [DecidableEq U]

abbrev cellFiber (cell : E → U) (u : U) := {e : E // cell e = u}

/-- h copies suffice precisely when every cell has at most h incidences. -/
theorem copies_iff_max_load (cell : E → U) (h : ℕ) :
    (∃ copy : E → Fin h, Function.Injective (fun e => (copy e, cell e))) ↔
      ∀ u, Fintype.card (cellFiber cell u) ≤ h := by
  classical
  constructor
  · rintro ⟨copy, hinj⟩ u
    have hf : Function.Injective (fun e : cellFiber cell u => copy e.val) := by
      intro e f hef
      exact Subtype.ext (hinj (Prod.ext hef (e.property.trans f.property.symm)))
    simpa using Fintype.card_le_of_injective _ hf
  · intro hh
    have hex (u : U) : Nonempty (cellFiber cell u ↪ Fin h) := by
      apply Function.Embedding.nonempty_of_card_le
      simpa using hh u
    let embed (u : U) : cellFiber cell u ↪ Fin h := Classical.choice (hex u)
    let copy (e : E) := embed (cell e) ⟨e, rfl⟩
    refine ⟨copy, ?_⟩
    intro e f hef
    have hc : cell e = cell f := congrArg Prod.snd hef
    have hf : copy e = copy f := congrArg Prod.fst hef
    unfold copy at hf
    have hcong (u u' : U) (he : cell e = u) (heq : u = u') :
        embed u ⟨e, he⟩ = embed u' ⟨e, he.trans heq⟩ := by
      subst u'
      rfl
    have hf' : embed (cell f) ⟨e, hc⟩ = embed (cell f) ⟨f, rfl⟩ :=
      (hcong _ _ rfl hc).symm.trans hf
    exact congrArg Subtype.val ((embed (cell f)).injective hf')

/-- The least copy count is the peak load of the specific layout. -/
theorem copies_at_peak (cell : E → U) :
    (∃ copy : E → Fin (univ.sup (fun u => Fintype.card (cellFiber cell u))),
        Function.Injective (fun e => (copy e, cell e))) ∧
      ∀ h, (∃ copy : E → Fin h, Function.Injective (fun e => (copy e, cell e))) →
        univ.sup (fun u => Fintype.card (cellFiber cell u)) ≤ h := by
  constructor
  · apply (copies_iff_max_load cell _).mpr
    intro u
    exact le_sup (f := fun u => Fintype.card (cellFiber cell u)) (mem_univ u)
  · intro h hc
    apply Finset.sup_le
    intro u _
    exact (copies_iff_max_load cell h).mp hc u

theorem peak_copy_volume (cell : E → U) (M : ℕ)
    (hcap : ∀ u, Fintype.card (cellFiber cell u) * Fintype.card U ≤ 2 * M) :
    univ.sup (fun u => Fintype.card (cellFiber cell u)) * Fintype.card U ≤ 2 * M := by
  classical
  by_cases he : (univ : Finset U).Nonempty
  · obtain ⟨u, _, hu⟩ := exists_mem_eq_sup (s := (univ : Finset U)) he
      (fun u => Fintype.card (cellFiber cell u))
    rw [hu]
    exact hcap u
  · simp [not_nonempty_iff_eq_empty.mp he]

/-- The grouped matrices keep every row, including all zero rows. -/
theorem grouped_row_budget {H I A : Type*} [Fintype H] [Fintype I] [DecidableEq I]
    [Fintype A] [LinearOrder A] (window : Finset ℕ) (D M b n : ℕ) (eps : ℝ)
    (heps : 0 ≤ eps) (hcopy : Fintype.card H * D ≤ 2 * M) (hM : M ≤ b * n)
    (hrows : (Fintype.card (Exceptional I A window) : ℝ) ≤ eps * D) :
    (Fintype.card (A × (H × Exceptional I A window)) : ℝ) ≤
      2 * (Fintype.card A : ℝ) * eps * b * n := by
  push_cast [Fintype.card_prod]
  have hc : (Fintype.card H : ℝ) * D ≤ 2 * (M : ℝ) := by exact_mod_cast hcopy
  have hm : (M : ℝ) ≤ (b : ℝ) * n := by exact_mod_cast hM
  calc
    _ ≤ (Fintype.card A : ℝ) * ((Fintype.card H : ℝ) * (eps * D)) := by gcongr
    _ = (Fintype.card A : ℝ) * eps * ((Fintype.card H : ℝ) * D) := by ring
    _ ≤ (Fintype.card A : ℝ) * eps * (2 * M) := by gcongr
    _ ≤ (Fintype.card A : ℝ) * eps * (2 * ((b : ℝ) * n)) := by gcongr
    _ = _ := by ring

/-- Constantly many factor words can obstruct a tuned layout even at linear M.
This counts the fibers after restricting the second word to the factor labels. -/
theorem support_obstruction {B C : Type*} [Fintype B] [Fintype C] [DecidableEq C]
    [DecidableEq B] (cell : E → B × C) (right : Finset C) (hM : 0 < Fintype.card E)
    (hright : ∀ e, (cell e).2 ∈ right)
    (hcap : ∀ u, Fintype.card (cellFiber cell u) * (Fintype.card B * Fintype.card C) ≤
      2 * Fintype.card E) :
    Fintype.card C ≤ 2 * right.card := by
  classical
  let allowed : Finset (B × C) := (univ : Finset B) ×ˢ right
  have hsum : Fintype.card E = ∑ u ∈ allowed, Fintype.card (cellFiber cell u) := by
    have he := card_eq_sum_card_fiberwise (s := (univ : Finset E)) (t := allowed)
      (f := cell) (fun e _ => by simp [allowed, hright])
    simpa only [card_univ, Fintype.card_subtype, cellFiber] using he
  have hb : 0 < Fintype.card B := by
    haveI : Nonempty E := Fintype.card_pos_iff.mp hM
    exact Fintype.card_pos_iff.mpr (Nonempty.map (fun e => (cell e).1) inferInstance)
  have h := calc
    Fintype.card E * (Fintype.card B * Fintype.card C) =
        ∑ u ∈ allowed, Fintype.card (cellFiber cell u) * (Fintype.card B * Fintype.card C) := by
          conv_lhs => rw [hsum, sum_mul]
    _ ≤ ∑ _u ∈ allowed, 2 * Fintype.card E := sum_le_sum fun u _ => hcap u
    _ = Fintype.card B * right.card * (2 * Fintype.card E) := by simp [allowed]
  have h' : Fintype.card E * Fintype.card B * Fintype.card C ≤
      (Fintype.card E * Fintype.card B) * (2 * right.card) := by
    convert h using 1 <;> ring
  exact Nat.le_of_mul_le_mul_left h' (Nat.mul_pos hM hb)

#print axioms copies_iff_max_load
#print axioms copies_at_peak
#print axioms peak_copy_volume
#print axioms grouped_row_budget
#print axioms support_obstruction

end Section6




