import A1R43LiteralGate
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8700000

/-! The accepted column cube is exactly one Boolean variable per
vertex of the input cubic graph. All extra physical columns have
only the pinned-zero assignment. -/
namespace A1R43Literal
open scoped Classical BigOperators
open J6R10Repack

noncomputable section

variable {V Pad : Type} [DecidableEq V]
variable (F : Finset (V×V))
local notation "N" => network F Pad

def colAccept (x : Wire F Pad→Bool) : Prop :=
  ∀ v : Col F Pad, colFlag F x v=true

def vertexLift (Pad : Type) (σ : V→Bool) : Wire F Pad→Bool
  | .inl (u,false) => σ (endpoint F u)
  | .inl (_,true) => false
  | .inr _ => false

theorem vertexLift_accepted (σ : V→Bool) :
    colAccept F (vertexLift F Pad σ) := by
  intro v
  rcases v with v|z
  · apply (col_eq F _ v).2
    intro u u'
    change σ (endpoint F u.val)=σ (endpoint F u'.val)
    rw [u.property,u'.property]
  · apply (col_dummy F _ z).2
    cases z <;> rfl

variable (positive : ∀ v, 0<GraphCutMoments.degree F v)

def firstIncident (v : V) : {u : Occ F//endpoint F u=v} :=
  Classical.choice (Nat.card_pos_iff.mp (by rw [incidence_card]; exact positive v)).1

def vertexRead (x : Wire F Pad→Bool) (v : V) : Bool :=
  x (evenWire F Pad (firstIncident F positive v).val)

theorem lift_read (x : Wire F Pad→Bool) (h : colAccept F x) :
    vertexLift F Pad (vertexRead F positive x)=x := by
  funext w
  rcases w with (⟨u,b⟩|z)
  · cases b
    · let v := endpoint F u
      exact (col_eq F x v).1 (h (.inl v)) (firstIncident F positive v) ⟨u,rfl⟩
    · exact ((col_dummy F x (.inl u)).1 (h (.inr (.inl u)))).symm
  · exact ((col_dummy F x (.inr z)).1 (h (.inr (.inr z)))).symm

omit [DecidableEq V] in
theorem vertexLift_even (σ : V→Bool) (u : Occ F) :
    vertexLift F Pad σ (evenWire F Pad u)=σ (endpoint F u) := rfl

def columnAssignments (Pad : Type) : (V→Bool) ≃ {x : Wire F Pad→Bool // colAccept F x} where
  toFun σ := ⟨vertexLift F Pad σ,vertexLift_accepted F σ⟩
  invFun x := vertexRead F positive x.val
  left_inv σ := by
    funext v
    change vertexRead F positive (vertexLift F Pad σ) v=σ v
    unfold vertexRead
    rw [vertexLift_even,(firstIncident F positive v).property]
  right_inv x := Subtype.ext (lift_read F positive x.val x.property)

def independent (σ : V→Bool) : Prop :=
  ∀ e : F, (!(σ e.val.1 && σ e.val.2))=true

def independentCount : ℕ := Nat.card {σ : V→Bool // independent F σ}

section Sum
variable {R : Type*} [CommRing R] [Fintype V] [Fintype Pad]

theorem colFlags_product (x : Wire F Pad→Bool) :
    (∏ v : Col F Pad,(spin (colFlag F x v):R))=(if colAccept F x then 1 else 0) := by
  by_cases h : colAccept F x
  · rw [if_pos h]
    refine Finset.prod_eq_one (fun v _=>?_ )
    unfold spin
    rw [h v]
    rfl
  · have hh : ∃ v : Col F Pad,colFlag F x v=false := by
      unfold colAccept at h
      push_neg at h
      obtain ⟨v,hv⟩:=h
      refine ⟨v,?_⟩
      cases hh : colFlag F x v <;> simp_all
    obtain ⟨v,hv⟩:=hh
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [spin,hv])

include positive in
theorem weighted_columns (h : (Wire F Pad→Bool)→R) :
    (∑ x : Wire F Pad→Bool, (∏ v : Col F Pad,spin (colFlag F x v)) * h x) =
      ∑ σ : V→Bool,h (vertexLift F Pad σ) := by
  simp only [colFlags_product]
  calc
    _ = ∑ x : Wire F Pad→Bool, if colAccept F x then h x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split <;> simp
    _ = ∑ x : {x : Wire F Pad→Bool // colAccept F x},h x.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun x=>by simp) h
    _ = _ := ((columnAssignments F positive Pad).sum_comp (fun x=>h x.val)).symm

omit [Fintype Pad] in
theorem independentCount_indicator :
    (independentCount F:R) = ∑ σ : V→Bool, if independent F σ then 1 else 0 := by
  rw [independentCount,Nat.card_eq_fintype_card,←Finset.sum_filter]
  have hc : (∑ _x ∈ Finset.univ.filter (independent F), (1:R)) =
      ∑ _x : {σ : V→Bool // independent F σ},(1:R) :=
    Finset.sum_subtype (p:=independent F) _ (fun x=>by simp) (fun _ : V→Bool=>(1:R))
  rw [hc]
  simp

omit [Fintype Pad] [DecidableEq V] [Fintype V] in
theorem NAND_product_indicator (σ : V→Bool) :
    (∏ e : F,(1-(spin (σ e.val.1):R)*spin (σ e.val.2))) =
      if independent F σ then 1 else 0 := by
  have hh (e : F) :
      (1-(spin (σ e.val.1):R)*spin (σ e.val.2))=spin (!(σ e.val.1 && σ e.val.2)) := by
    cases σ e.val.1 <;> cases σ e.val.2 <;> simp [spin]
  simp_rw [hh]
  by_cases hx : independent F σ
  · rw [if_pos hx]
    refine Finset.prod_eq_one (fun e _=>?_ )
    unfold spin
    rw [hx e]
    rfl
  · rw [if_neg hx]
    have hn : ∃ e : F, (!(σ e.val.1 && σ e.val.2))=false := by
      unfold independent at hx
      push_neg at hx
      obtain ⟨e,he⟩:=hx
      refine ⟨e,?_⟩
      cases hb : !(σ e.val.1 && σ e.val.2) <;> simp_all
    obtain ⟨e,he⟩:=hn
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by unfold spin; rw [he]; rfl)

end Sum

#print axioms vertexLift_accepted
#print axioms firstIncident
#print axioms lift_read
#print axioms columnAssignments
#print axioms colFlags_product
#print axioms weighted_columns
#print axioms independentCount_indicator
#print axioms NAND_product_indicator

end
end A1R43Literal
