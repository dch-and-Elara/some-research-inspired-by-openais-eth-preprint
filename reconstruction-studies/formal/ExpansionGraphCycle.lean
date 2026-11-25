import ExpansionGraphBase
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Reconstruction.ExpansionGraph

open Finset
open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Port := ZMod 32

private theorem port_card : Fintype.card Port = 32 := ZMod.card 32

private theorem one_ne_zero_port : (1 : Port) ≠ 0 := by decide
private theorem two_ne_zero_port : (2 : Port) ≠ 0 := by decide

/-- Each old incident edge gets its own port on the 32-cycle. -/
def portAssignment (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ v, G.degree v ≤ 32)
    (v : V) : G.neighborSet v ↪ Port :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    rw [G.card_neighborSet_eq_degree, port_card]
    exact hd v))

private def cycleAdj (a b : V × Port) : Prop :=
  a.1 = b.1 ∧ (b.2 = a.2 + 1 ∨ a.2 = b.2 + 1)

private def externalAdj (G : SimpleGraph V) (p : ∀ v, G.neighborSet v ↪ Port)
    (a b : V × Port) : Prop :=
  ∃ h : G.Adj a.1 b.1, p a.1 ⟨b.1,h⟩ = a.2 ∧ p b.1 ⟨a.1,h.symm⟩ = b.2

/-- Replace the vertex by a 32-cycle and attach each old edge at its assigned ports. -/
def replaceByCycles (G : SimpleGraph V) (p : ∀ v, G.neighborSet v ↪ Port) :
    SimpleGraph (V × Port) where
  Adj a b := cycleAdj a b ∨ externalAdj G p a b
  symm := by
    intro a b h
    rcases h with ⟨he,h⟩ | ⟨he,h₁,h₂⟩
    · exact Or.inl ⟨he.symm,h.symm⟩
    · exact Or.inr ⟨he.symm,h₂,h₁⟩
  loopless := by
    intro a h
    rcases h with ⟨_,h|h⟩ | ⟨h,_,_⟩
    · exact one_ne_zero_port (by linear_combination -h)
    · exact one_ne_zero_port (by linear_combination -h)
    · exact h.ne rfl

omit [Fintype V] [DecidableEq V] in
private theorem externalAdj_unique {G : SimpleGraph V} {p : ∀ v, G.neighborSet v ↪ Port}
    {a b c : V × Port} (hb : externalAdj G p a b) (hc : externalAdj G p a c) : b = c := by
  obtain ⟨hb, hb₁, hb₂⟩ := hb
  obtain ⟨hc, hc₁, hc₂⟩ := hc
  have hv : b.1 = c.1 := congrArg Subtype.val ((p a.1).injective (hb₁.trans hc₁.symm))
  rcases b with ⟨b,i⟩
  rcases c with ⟨c,j⟩
  change b = c at hv
  subst c
  exact Prod.ext rfl (hb₂.symm.trans hc₂)

theorem replacement_degree (G : SimpleGraph V) (p : ∀ v, G.neighborSet v ↪ Port)
    (a : V × Port) :
    let H := replaceByCycles G p
    letI : DecidableRel H.Adj := Classical.decRel _
    2 ≤ H.degree a ∧ H.degree a ≤ 3 := by
  classical
  let H := replaceByCycles G p
  letI : DecidableRel H.Adj := Classical.decRel _
  let C : Finset (V × Port) := {(a.1,a.2+1), (a.1,a.2-1)}
  let E : Finset (V × Port) := univ.filter fun b => externalAdj G p a b
  have hC : C.card = 2 := by
    have hn : (a.1,a.2+1) ≠ (a.1,a.2-1) := by
      intro eq
      have h := congrArg Prod.snd eq
      exact two_ne_zero_port (by change a.2+1 = a.2-1 at h; linear_combination h)
    simp [C, hn]
  have hE : E.card ≤ 1 := by
    refine card_le_one.mpr fun b hb c hc => externalAdj_unique (G := G) (p := p) (a := a) ?_ ?_
    · exact (mem_filter.mp hb).2
    · exact (mem_filter.mp hc).2
  have heq : H.neighborFinset a = C ∪ E := by
    ext b
    rw [H.mem_neighborFinset a b, mem_union]
    have hc : cycleAdj a b ↔ b ∈ C := by
      constructor
      · rintro ⟨h1,h|h⟩
        · exact mem_insert.mpr (Or.inl (Prod.ext h1.symm h))
        · have h' : b.2 = a.2 - 1 := eq_sub_of_add_eq h.symm
          exact mem_insert.mpr (Or.inr (mem_singleton.mpr (Prod.ext h1.symm h')))
      · intro h
        rcases mem_insert.mp h with he | he
        · cases he
          exact ⟨rfl, Or.inl rfl⟩
        · have he' := mem_singleton.mp he
          cases he'
          exact ⟨rfl, Or.inr (by exact (sub_add_cancel a.2 1).symm)⟩
    change cycleAdj a b ∨ externalAdj G p a b ↔ b ∈ C ∨ b ∈ E
    simp only [E, hc, mem_filter, mem_univ, true_and]
  change 2 ≤ (H.neighborFinset a).card ∧ (H.neighborFinset a).card ≤ 3
  rw [heq]
  have hl := card_le_card (subset_union_left (s₁ := C) (s₂ := E))
  have hh := card_union_le C E
  omega

private theorem exists_cycle_step {S : Port → Prop}
    (hin : ∃ a, S a) (hout : ∃ b, ¬ S b) : ∃ a, S a ∧ ¬ S (a+1) := by
  by_contra! h
  obtain ⟨a,ha⟩ := hin
  obtain ⟨b,hb⟩ := hout
  have hiter (n : ℕ) : S (a + (n : Port)) := by
    induction n with
    | zero => simpa using ha
    | succ n ih => simpa only [Nat.cast_succ, add_assoc] using h (a + (n : Port)) ih
  have hh := hiter (b-a).val
  rw [ZMod.natCast_zmod_val, add_sub_cancel] at hh
  exact hb hh

private theorem exists_split_steps {S : Port → Prop} (hin : ∃ a, S a) (hout : ∃ b, ¬ S b) :
    ∃ a b, S a ∧ ¬ S (a+1) ∧ ¬ S b ∧ S (b+1) := by
  obtain ⟨a, ha, ha'⟩ := exists_cycle_step hin hout
  obtain ⟨b, hb, hb'⟩ := exists_cycle_step (S := fun a => ¬ S a) hout
    (by obtain ⟨c,hc⟩ := hin; exact ⟨c,not_not_intro hc⟩)
  exact ⟨a,b,ha,ha',hb,not_not.mp hb'⟩

private def cycleFull (U : Finset (V × Port)) : Finset V := by
  classical
  exact univ.filter fun v => ∀ i : Port, (v,i) ∈ U

private def cycleHit (U : Finset (V × Port)) : Finset V := by
  classical
  exact univ.filter fun v => ∃ i : Port, (v,i) ∈ U

private def cycleSplit (U : Finset (V × Port)) : Finset V := cycleHit U \ cycleFull U

private theorem full_subset_hit (U : Finset (V × Port)) : cycleFull U ⊆ cycleHit U := by
  classical
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _, 0, (mem_filter.mp hv).2 0⟩

private theorem cycleCount_bounds (U : Finset (V × Port)) :
    32*(cycleFull U).card ≤ U.card ∧ U.card ≤ 32*(cycleHit U).card := by
  classical
  have hf : (cycleFull U).product (univ : Finset Port) ⊆ U := by
    intro v hv
    exact (mem_filter.mp (mem_product.mp hv).1).2 v.2
  have hh : U ⊆ (cycleHit U).product (univ : Finset Port) := by
    intro v hv
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,v.2,hv⟩,mem_univ _⟩
  have hF : ((cycleFull U) ×ˢ (univ : Finset Port)).card ≤ U.card := card_le_card hf
  have hH : U.card ≤ ((cycleHit U) ×ˢ (univ : Finset Port)).card := card_le_card hh
  rw [card_product, card_univ, port_card] at hF hH
  exact ⟨by simpa [mul_comm] using hF, by simpa [mul_comm] using hH⟩

private theorem split_supplies_edges (G : SimpleGraph V) (p : ∀ v, G.neighborSet v ↪ Port)
    (U : Finset (V × Port)) :
    2*(cycleSplit U).card ≤ (crossingEdges (replaceByCycles G p) U).card := by
  classical
  have hex (v : ↥(cycleSplit U)) : ∃ a b : Port,
      (v.val,a) ∈ U ∧ (v.val,a+1) ∉ U ∧ (v.val,b) ∉ U ∧ (v.val,b+1) ∈ U := by
    have hv := mem_sdiff.mp v.property
    exact exists_split_steps ((mem_filter.mp hv.1).2) (by
      by_contra! h
      exact hv.2 (mem_filter.mpr ⟨mem_univ _,h⟩))
  choose a b h using hex
  let f (w : ↥(cycleSplit U) × Bool) : ↥(crossingEdges (replaceByCycles G p) U) :=
    if w.2 then
      ⟨((w.1.val,a w.1),(w.1.val,a w.1+1)),
        mem_crossingEdges.mpr ⟨Or.inl ⟨rfl,Or.inl rfl⟩,(h w.1).1,(h w.1).2.1⟩⟩
    else
      ⟨((w.1.val,b w.1+1),(w.1.val,b w.1)),
        mem_crossingEdges.mpr ⟨Or.inl ⟨rfl,Or.inr rfl⟩,(h w.1).2.2.2,(h w.1).2.2.1⟩⟩
  have hinj : Function.Injective f := by
    rintro ⟨v,i⟩ ⟨w,j⟩ he
    have hv : v = w := by
      apply Subtype.ext
      have H := congrArg (fun e : ↥(crossingEdges (replaceByCycles G p) U) => e.val.1.1) he
      cases i <;> cases j <;> exact H
    subst w
    have he1 := congrArg (fun e : ↥(crossingEdges (replaceByCycles G p) U) => e.val.1.2) he
    have he2 := congrArg (fun e : ↥(crossingEdges (replaceByCycles G p) U) => e.val.2.2) he
    apply Prod.ext (show v = v from rfl)
    cases i <;> cases j
    · rfl
    · change b v+1 = a v at he1
      change b v = a v+1 at he2
      exact (two_ne_zero_port (by linear_combination he1 - he2)).elim
    · change a v = b v+1 at he1
      change a v+1 = b v at he2
      exact (two_ne_zero_port (by linear_combination he2 - he1)).elim
    · rfl
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, mul_comm] using
    Fintype.card_le_of_injective f hinj

private theorem round_cut (U : Finset (V × Port))
    (h4 : 4 ∣ Fintype.card V)
    (hlo : Fintype.card V * 32 ≤ 4*U.card) (hhi : 2*U.card ≤ Fintype.card V * 32) :
    ∃ B : Finset V, cycleFull U ⊆ B ∧ B ⊆ cycleHit U ∧
      Fintype.card V ≤ 4*B.card ∧ 2*B.card ≤ Fintype.card V := by
  classical
  let m := Fintype.card V
  let f := (cycleFull U).card
  let h := (cycleHit U).card
  let b := max (m/4) f
  obtain ⟨hf,hh⟩ := cycleCount_bounds U
  have hfh : f ≤ h := card_le_card (full_subset_hit U)
  have hdvd : m/4*4 = m := Nat.div_mul_cancel h4
  have hcount : (cycleSplit U).card + f = h :=
    card_sdiff_add_card_eq_card (full_subset_hit U)
  have hh' : b - f ≤ (cycleSplit U).card := by omega
  obtain ⟨A, hA, hAc⟩ := exists_subset_card_eq hh'
  have hdis : Disjoint (cycleFull U) A := by
    apply disjoint_left.mpr
    intro v hv hv'
    exact (mem_sdiff.mp (hA hv')).2 hv
  let B := cycleFull U ∪ A
  have hc : B.card = b := by
    rw [card_union_of_disjoint hdis, hAc]
    exact Nat.add_sub_of_le (le_max_right ..)
  refine ⟨B, subset_union_left, union_subset (full_subset_hit U) (hA.trans sdiff_subset), ?_, ?_⟩
  · rw [hc]
    omega
  · rw [hc]
    omega

private theorem charge_split_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : ∀ v, G.degree v ≤ 32) (B S : Finset V) :
    (((crossingEdges G B).filter fun e => e.1 ∈ S ∨ e.2 ∈ S).card) ≤ 32 * S.card := by
  classical
  let O := (crossingEdges G B).filter fun e => e.1 ∈ S ∨ e.2 ∈ S
  let dest := Σ v : S, G.neighborSet v.val
  let f (e : O) : dest := by
    have hx := mem_filter.mp e.property
    have ha := (mem_crossingEdges.mp hx.1).1
    by_cases h : e.val.1 ∈ S
    · exact ⟨⟨e.val.1,h⟩,⟨e.val.2,ha⟩⟩
    · exact ⟨⟨e.val.2,hx.2.resolve_left h⟩,⟨e.val.1,ha.symm⟩⟩
  let decode (x : dest) : V × V :=
    if x.1.val ∈ B then (x.1.val,x.2.val) else (x.2.val,x.1.val)
  have hInv (e : O) : decode (f e) = e.val := by
    have hx := mem_crossingEdges.mp (mem_filter.mp e.property).1
    dsimp [f]
    split <;> simp [decode, hx.2.1, hx.2.2]
  have hf : Function.Injective f := fun x y e => Subtype.ext (by rw [← hInv x, ← hInv y, e])
  calc
    _ ≤ Fintype.card dest := by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
    _ = ∑ v : S, G.degree v := by
      unfold dest
      rw [Fintype.card_sigma]
      simp only [G.card_neighborSet_eq_degree]
    _ ≤ ∑ _v : S, 32 := sum_le_sum fun _ _ => hd _
    _ = _ := by simp [mul_comm]

private theorem kept_external_crossings (G : SimpleGraph V) (p : ∀ v, G.neighborSet v ↪ Port)
    (U : Finset (V × Port)) (B : Finset V)
    (hFull : cycleFull U ⊆ B) (hHit : B ⊆ cycleHit U) :
    (((crossingEdges G B).filter fun e => ¬ (e.1 ∈ cycleSplit U ∨ e.2 ∈ cycleSplit U)).card) ≤
      (crossingEdges (replaceByCycles G p) U).card := by
  classical
  let T := (crossingEdges G B).filter fun e => ¬ (e.1 ∈ cycleSplit U ∨ e.2 ∈ cycleSplit U)
  let f (x : T) : ↥(crossingEdges (replaceByCycles G p) U) := by
    have hx := (mem_filter.mp x.property).1
    have hns := (mem_filter.mp x.property).2
    have he := (mem_crossingEdges.mp hx).1
    have hu := (mem_crossingEdges.mp hx).2.1
    have hv := (mem_crossingEdges.mp hx).2.2
    let a := (x.val.1, p x.val.1 ⟨x.val.2,he⟩)
    let b := (x.val.2, p x.val.2 ⟨x.val.1,he.symm⟩)
    have ha : x.val.1 ∈ cycleFull U := by
      by_contra hn
      exact hns (Or.inl (mem_sdiff.mpr ⟨hHit hu,hn⟩))
    have hb : x.val.2 ∉ cycleHit U := by
      intro hm
      exact hns (Or.inr (mem_sdiff.mpr ⟨hm,fun h => hv (hFull h)⟩))
    exact ⟨(a,b),mem_crossingEdges.mpr ⟨Or.inr ⟨he,rfl,rfl⟩, (mem_filter.mp ha).2 _,
      fun h => hb (mem_filter.mpr ⟨mem_univ _,_,h⟩)⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    have H := congrArg (fun e : ↥(crossingEdges (replaceByCycles G p) U) => (e.val.1.1,e.val.2.1)) he
    change (x.val.1,x.val.2) = (y.val.1,y.val.2) at H
    exact H
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- The two cases of the cut proof: two cycle edges per split cycle, or
the rounded old cut with at most 32 lost edges per split cycle. -/
theorem replacement_balanced (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : ∀ v, G.degree v ≤ 32) (p : ∀ v, G.neighborSet v ↪ Port)
    (h4 : 4 ∣ Fintype.card V)
    (hG : ∀ B : Finset V, Fintype.card V ≤ 4*B.card → 2*B.card ≤ Fintype.card V →
      Fintype.card V ≤ 32*(crossingEdges G B).card) :
    HasBalancedCuts (replaceByCycles G p) := by
  classical
  intro U hlo hhi
  simp only [Fintype.card_prod, port_card] at hlo hhi ⊢
  let S := cycleSplit U
  by_cases hlarge : Fintype.card V ≤ 2048*S.card
  · have hs : 2*S.card ≤ (crossingEdges (replaceByCycles G p) U).card := split_supplies_edges G p U
    omega
  · obtain ⟨B, hFull, hHit, hb₁, hb₂⟩ := round_cut U h4 hlo hhi
    let O := crossingEdges G B
    let good := O.filter fun e => ¬ (e.1 ∈ S ∨ e.2 ∈ S)
    let bad := O.filter fun e => e.1 ∈ S ∨ e.2 ∈ S
    have hsum : bad.card + good.card = O.card := card_filter_partition _ _
    have hbad : bad.card ≤ 32*S.card := charge_split_edges G hd B S
    have hgood : good.card ≤ (crossingEdges (replaceByCycles G p) U).card :=
      kept_external_crossings G p U B hFull hHit
    have hc : Fintype.card V ≤ 32 * O.card := hG B hb₁ hb₂
    omega

end

end Reconstruction.ExpansionGraph
