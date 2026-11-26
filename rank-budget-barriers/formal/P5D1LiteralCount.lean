import P5D1LiteralOldRows

/-! The actual source tables give exactly the original four-clone count
after reduction at the original creation precision. This uses the
two incidence wires and each directed cycle, not a copied scalar result. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R9Recursive Paper5.HybridClosure

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
local notation "N" => dNetwork F cubic

def OldRowOK (σ : W → Bool) (x : DWire F → Bool) : Prop :=
  ∀ v, oldRowTruth F cubic σ v (assignment N x v) = true

noncomputable def copyAssignment (σ : W → Bool) (e : DWire F) : Bool :=
  σ (cloneOwner F cubic e.1).1

noncomputable def cloneRead (x : DWire F → Bool) (u : Clone W) : Bool :=
  x ((occChart F cubic).symm (u,.inl ()),false)

theorem forward_col {σ : W → Bool} {x : DWire F → Bool}
    (hx : OldRowOK F cubic σ x) (p : MainClonedCNF.Port F) :
    x (p,false) = x (p,true) := by
  have h := hx (.inr p)
  change decide (x (p,false)=x (p,true)) = true at h
  exact of_decide_eq_true h

theorem forward_old_clone {σ : W → Bool} {x : DWire F → Bool}
    (hx : OldRowOK F cubic σ x) (p q : MainClonedCNF.Port F)
    (same : cloneOwner F cubic p=cloneOwner F cubic q) : x (p,false) = x (q,false) := by
  have h := hx (.inl (.inl (cloneOwner F cubic p)))
  change decide (∀ a b : ParentPorts N (.inl (.inl (cloneOwner F cubic p))),
    assignment N x _ a = assignment N x _ b) = true at h
  exact (of_decide_eq_true h)
    ⟨.inl (p,false),rfl⟩ ⟨.inl (q,false),congrArg (fun w : Clone W => (Sum.inl (Sum.inl w) : DOld F ⊕ MainClonedCNF.Port F)) same.symm⟩

theorem forward_read {σ : W → Bool} {x : DWire F → Bool}
    (hx : OldRowOK F cubic σ x) (p : MainClonedCNF.Port F) (b : Bool) :
    x (p,b) = cloneRead F cubic x (cloneOwner F cubic p) := by
  have he : cloneOwner F cubic p =
      cloneOwner F cubic ((occChart F cubic).symm (cloneOwner F cubic p,.inl ())) :=
    (congrArg Prod.fst ((occChart F cubic).apply_symm_apply (cloneOwner F cubic p,.inl ()))).symm
  have hh := forward_old_clone F cubic hx p _ he
  cases b
  · exact hh
  · exact (forward_col F cubic hx p).symm.trans hh

private theorem compatible_cycle (b : Fin 4 → Bool)
    (h : ∀j, (!b j || b (j+1)) = true) (j : Fin 4) : b j = b 0 := by
  have g : ∀ a b c d : Bool,
      (!a || b)=true → (!b || c)=true → (!c || d)=true → (!d || a)=true →
      b=a ∧ c=a ∧ d=a := by decide
  have e := g (b 0) (b 1) (b 2) (b 3) (h 0) (h 1) (h 2) (h 3)
  fin_cases j
  · rfl
  · exact e.1
  · exact e.2.1
  · exact e.2.2

theorem forward_pin {σ : W → Bool} {x : DWire F → Bool}
    (hx : OldRowOK F cubic σ x) (v : W) :
    cloneRead F cubic x (v,0) = σ v := by
  have h := hx (.inl (.inr (.inl v)))
  change decide (x ((.inl v),true)=σ v) = true at h
  exact (forward_read F cubic hx (.inl v) true).symm.trans (of_decide_eq_true h)

theorem forward_cycle {σ : W → Bool} {x : DWire F → Bool}
    (hx : OldRowOK F cubic σ x) (v : W) (j : Fin 4) :
    cloneRead F cubic x (v,j) = cloneRead F cubic x (v,0) := by
  apply compatible_cycle (fun j => cloneRead F cubic x (v,j)) _ j
  intro k
  have h := hx (.inl (.inr (.inr (.inr (v,k)))))
  change (!(x ((.inr (.inr (v,k,false))),true)) ||
    x ((.inr (.inr (v,k,true))),true)) = true at h
  rw [forward_read F cubic hx (.inr (.inr (v,k,false))) true,
    forward_read F cubic hx (.inr (.inr (v,k,true))) true] at h
  exact h

theorem forward_assignment {σ : W → Bool} {x : DWire F → Bool}
    (hx : OldRowOK F cubic σ x) : x = copyAssignment F cubic σ := by
  funext p
  rcases p with ⟨p,b⟩
  exact (forward_read F cubic hx p b).trans
    ((forward_cycle F cubic hx _ _).trans (forward_pin F cubic hx _))

omit [Fintype W] in
theorem oldRow_port_clone (z : Clone W)
    (p : ParentPorts N (.inl (.inl z))) :
    cloneOwner F cubic (edge p.val).1 = z := by
  obtain ⟨p,h⟩ := p
  rcases p with p|p
  · rcases p with ⟨p,b⟩
    cases b
    · exact Sum.inl.inj (Sum.inl.inj h)
    · simp [owner,dNetwork] at h
  · simp [owner] at h

theorem oldRow_OK_iff (σ : W → Bool) (x : DWire F → Bool) :
    OldRowOK F cubic σ x ↔ x = copyAssignment F cubic σ ∧ PinnedCNF.AllEdges F σ := by
  constructor
  · intro h
    have hx := forward_assignment F cubic h
    refine ⟨hx,?_⟩
    intro e he
    have h₁ := h (.inl (.inr (.inr (.inl ⟨e,he⟩))))
    change (x ((.inr (.inl (⟨e,he⟩,false))),true) ||
      x ((.inr (.inl (⟨e,he⟩,true))),true)) = true at h₁
    rw [hx] at h₁
    simpa [copyAssignment,edge_owner_left,edge_owner_right,Bool.or_eq_true] using h₁
  · rintro ⟨rfl,h⟩ v
    rcases v with (u|v|e|⟨v,j⟩)|e
    · change decide (∀ (p q : ParentPorts N (.inl (.inl u))),
        copyAssignment F cubic σ (edge p.val) = copyAssignment F cubic σ (edge q.val)) = true
      apply decide_eq_true
      intro p q
      unfold copyAssignment
      rw [oldRow_port_clone F cubic u p,oldRow_port_clone F cubic u q]
    · change decide (σ v=σ v) = true
      simp
    · change (copyAssignment F cubic σ ((.inr (.inl (e,false))),true) ||
        copyAssignment F cubic σ ((.inr (.inl (e,true))),true)) = true
      simp only [copyAssignment,edge_owner_left,edge_owner_right,Bool.or_eq_true]
      exact h e.val e.property
    · change (!σ v || σ v)=true
      cases σ v <;> decide
    · change decide (σ (cloneOwner F cubic e).1 = σ (cloneOwner F cubic e).1) = true
      simp

set_option maxHeartbeats 2100000 in
theorem oldRow_contraction_reduce (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (σ : W → Bool) :
    reduce p f 1 (trueContraction N (oldRowFile F cubic f p σ) hf) =
      (PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F cubic)
        (MainClonedCNF.rightSlot F cubic) σ) : Residue f 1 p) := by
  classical
  unfold trueContraction
  rw [map_sum, MainClonedCNF.modelCount_cloned, PinnedCNF.count_eq_indicator]
  trans ∑ x : DWire F → Bool,
    if OldRowOK F cubic σ x then (1:Residue f 1 p) else 0
  · apply Finset.sum_congr rfl
    intro x _
    rw [map_prod]
    have hh (v : DOld F ⊕ MainClonedCNF.Port F) :
        reduce p f 1 ((oldRowFile F cubic f p σ v).frozen hf (assignment N x v)) =
          if oldRowTruth F cubic σ v (assignment N x v) then 1 else 0 :=
      CreatedEntry.read_created (oldRowFile F cubic f p σ v) hf (assignment N x v)
    simp_rw [hh]
    by_cases h : OldRowOK F cubic σ x
    · rw [if_pos h]
      simp only [show ∀v, oldRowTruth F cubic σ v (assignment N x v) = true from h,
        if_true,Finset.prod_const_one]
    · rw [if_neg h]
      have hq : ∃ v : DOld F ⊕ MainClonedCNF.Port F,
          oldRowTruth F cubic σ v (assignment N x v) = false := by
        simpa only [OldRowOK,not_forall,Bool.not_eq_true] using h
      obtain ⟨v,hv⟩ := hq
      apply Finset.prod_eq_zero (i:=v) (Finset.mem_univ v)
      simp [hv]
  · simp_rw [oldRow_OK_iff F cubic]
    by_cases h : PinnedCNF.AllEdges F σ <;> simp [h]

#print axioms forward_col
#print axioms forward_old_clone
#print axioms forward_read
#print axioms forward_pin
#print axioms forward_cycle
#print axioms oldRow_port_clone
#print axioms oldRow_OK_iff
#print axioms oldRow_contraction_reduce
end Paper5.D1Literal
