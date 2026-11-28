import LayoutMomentsPrincipal
import LayoutMomentsMismatch

/-! Literal occurrence-list interpretation of the candidate factors in
Paper 2, §3. Tagging by the slot preserves repetitions without changing
any physical variable, measurement row, output coefficient or layout. -/
namespace Reconstruction.LayoutMoments.PublishedCandidateList

open Polynomial
open LayoutBudget (GroupFiber measurementRank)
open scoped BigOperators Polynomial Classical
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

def slotTag {F : Type*} (xs : List F) : Fin xs.length ↪ F × ℕ where
  toFun i := (xs.get i,i.val)
  inj' := by
    intro i j eq
    exact Fin.ext (congrArg Prod.snd eq)

def taggedMenu {F : Type*} (xs : List F) : Finset (F × ℕ) :=
  Finset.univ.map (slotTag xs)

theorem taggedMenu_card {F : Type*} (xs : List F) :
    (taggedMenu xs).card = xs.length := by
  simp [taggedMenu]

theorem taggedMenu_nonempty {F : Type*} (xs : List F) (h : 0 < xs.length) :
    (taggedMenu xs).Nonempty :=
  Finset.card_pos.mp (by simpa only [taggedMenu_card] using h)

theorem taggedMenu_sum {F S : Type*} [AddCommMonoid S] (xs : List F) (value : F → S) :
    (∑ f ∈ taggedMenu xs, value f.1) = ∑ i : Fin xs.length, value (xs.get i) := by
  exact Finset.sum_map (Finset.univ : Finset (Fin xs.length)) (slotTag xs) (fun f => value f.1)

theorem taggedMenu_scope {F : Type*} (xs : List F) (scope : F → Prop)
    (h : ∀ i : Fin xs.length, scope (xs.get i)) {f : F × ℕ}
    (hf : f ∈ taggedMenu xs) : scope f.1 := by
  change f ∈ (Finset.univ : Finset (Fin xs.length)).map (slotTag xs) at hf
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hf
  exact h i

variable {V I G Factor : Type*} [DecidableEq V] [Fintype G] [DecidableEq G]
variable {M : I → G → Type*} [∀ t g, Fintype (M t g)]
variable (V₀ : Finset V) (T : Finset I) (node : I → ℚ) (R : ℕ)
variable (a : I → V → G) (b : I → Factor → G) (scope : Factor → V → Prop)
variable (P : Factor → V → V → ℚ[X])
variable (C : ∀ t g, Matrix (M t g) (GroupFiber (a t) g) ℚ)
variable (menu : V₀ → List Factor) (δ : ℝ) (Δ : ℕ)
variable (hV : V₀.Nonempty)
variable (hne : ∀ v, 0 < (menu v).length) (hsize : ∀ v, (menu v).length ≤ Δ)
variable (hscope : ∀ v (i : Fin (menu v).length), scope ((menu v).get i) v.val)
variable (hdemand : ∀ t ∈ T, δ*(V₀.card:ℝ) ≤
  ∑ v : V₀, ∑ i : Fin (menu v).length, if a t v.val ≠ b t ((menu v).get i) then (1:ℝ) else 0)
variable (hnodes : Set.InjOn node (↑T : Set I))
variable (hzero : ∀ f v, scope f v → ∀ w, (P f v w).eval 0 = if v = w then 1 else 0)
variable (hdegree : ∀ f v, scope f v → ∀ w, (P f v w).natDegree ≤ R)
variable (hforeign : ∀ t ∈ T, ∀ f v, scope f v → ∀ g, b t f ≠ g →
  (fun w : GroupFiber (a t) g => (P f v w.val).eval (node t)) ∈
    Submodule.span ℚ (Set.range (C t g).row))

include hV hne hsize hscope hdemand hnodes hzero hdegree hforeign in
/-- Equation (5) for literal lists with repeated candidates counted
by their occurrences. The constants and the physical measurement ranks
are unchanged. -/
theorem corollary_two_literal_lists (gmax : ℕ) (hT : T.Nonempty)
    (hgroups : ∀ t ∈ T, ∀ g, Fintype.card (GroupFiber (fun v : V₀ => a t v.val) g) ≤ gmax) :
    (δ/(Δ:ℝ))*(V₀.card:ℝ)/(48*Real.sqrt (2*(gmax:ℝ))) ≤
      (∑ t : T, (measurementRank (fun v : V₀ => v.val) (a t) (C t):ℝ))/(T.card:ℝ) +
        (V₀.card:ℝ)*R/(2*(T.card:ℝ)) := by
  refine corollary_two V₀ T node R a (fun t (f : Factor × ℕ) => b t f.1)
    (fun f v => scope f.1 v) (fun f v w => P f.1 v w) C
    (fun v => taggedMenu (menu v)) δ Δ gmax hV hT
    (fun v => taggedMenu_nonempty _ (hne v)) (fun v => (taggedMenu_card _).trans_le (hsize v))
    (fun v _ h => taggedMenu_scope (menu v) (fun f => scope f v.val) (hscope v) h) ?_ hgroups
    hnodes (fun f => hzero f.1) (fun f => hdegree f.1) (fun t ht f => hforeign t ht f.1)
  intro t ht
  refine (hdemand t ht).trans_eq ?_
  apply Finset.sum_congr rfl
  intro v _
  exact (taggedMenu_sum (menu v) (fun f => if a t v.val ≠ b t f then (1:ℝ) else 0)).symm

include hV hne hsize hscope hdemand hnodes hzero hdegree hforeign in
/-- Equation (10), including the individual-node multiplicity, for the
same literal list convention. -/
theorem corollary_five_literal_lists [DecidableEq I] (hδ : 0 < δ)
    (hnonzero : ∀ t ∈ T, node t ≠ 0)
    (hwindow : nodeWindow (δ/(Δ:ℝ)) R ≤ T.card) :
    let β := δ/(Δ:ℝ)
    let k := nodeWindow β R
    let B := rankConstant β*(V₀.card:ℝ)/((R:ℝ)+1)
    let m (t : I) : ℝ := measurementRank (fun v : V₀ => v.val) (a t) (C t)
    0 < windowConstant β ∧ 0 < rankConstant β ∧
      (∀ S ⊆ T, S.card = k → B ≤ (∑ t ∈ S, m t)/(k:ℝ)) ∧
      T.card-k+1 ≤ (T.filter fun t => B ≤ m t).card := by
  refine corollary_five V₀ T node R a (fun t (f : Factor × ℕ) => b t f.1)
    (fun f v => scope f.1 v) (fun f v w => P f.1 v w) C
    (fun v => taggedMenu (menu v)) δ Δ hV hδ
    (fun v => taggedMenu_nonempty _ (hne v)) (fun v => (taggedMenu_card _).trans_le (hsize v))
    (fun v _ h => taggedMenu_scope (menu v) (fun f => scope f v.val) (hscope v) h) ?_ hnodes hnonzero
    (fun f => hzero f.1) (fun f => hdegree f.1) (fun t ht f => hforeign t ht f.1) hwindow
  intro t ht
  refine (hdemand t ht).trans_eq ?_
  apply Finset.sum_congr rfl
  intro v _
  exact (taggedMenu_sum (menu v) (fun f => if a t v.val ≠ b t f then (1:ℝ) else 0)).symm

#print axioms taggedMenu_card
#print axioms taggedMenu_nonempty
#print axioms taggedMenu_scope
#print axioms taggedMenu_sum
#print axioms corollary_two_literal_lists
#print axioms corollary_five_literal_lists
end Reconstruction.LayoutMoments.PublishedCandidateList

