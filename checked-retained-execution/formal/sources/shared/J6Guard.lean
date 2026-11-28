import PinnedCNF
import LayerRecovery
import Mathlib.Tactic

/-! Literal J6 padding guard. The guard is a genuine width-four CNF on
the original declared variable type plus one fresh variable. Empty or
tautological input clauses do not invalidate the counting identity. -/
namespace J6Guard
open Std.Sat
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def extendAssignment (z : Bool) (x : V → Bool) : Option V → Bool :=
  fun v => v.elim z x

def mapLit (p : V × Bool) : Option V × Bool := (some p.1,p.2)

noncomputable def guardedFormula (F : CNF V) : CNF (Option V) :=
  (F.map (fun c => (none,false) :: c.map mapLit)) ++
    (Finset.univ.toList.map (fun v : V => [(none,true),(some v,false)]))

omit [Fintype V] [DecidableEq V] in
private theorem guardedClause_eval (z : Bool) (x : V → Bool) (c : CNF.Clause V) :
    CNF.Clause.eval (extendAssignment z x) ((none,false)::c.map mapLit) =
      (!z || c.eval x) := by
  cases z <;> simp [CNF.Clause.eval,List.any_map,Function.comp_def,extendAssignment,mapLit]

omit [Fintype V] [DecidableEq V] in
private theorem restriction_eval (z : Bool) (x : V → Bool) (v : V) :
    CNF.Clause.eval (extendAssignment z x) [(none,true),(some v,false)] = (z || !x v) := by
  cases z <;> cases h : x v <;> simp [CNF.Clause.eval,extendAssignment,h]

omit [DecidableEq V] in
theorem guardedFormula_eval (F : CNF V) (z : Bool) (x : V → Bool) :
    (guardedFormula F).eval (extendAssignment z x) = LayerRecovery.guard F.eval z x := by
  classical
  cases z
  · apply Bool.eq_iff_iff.mpr
    simp [guardedFormula,CNF.eval,List.all_map,Function.comp_def,LayerRecovery.guard,
      CNF.Clause.eval,extendAssignment,mapLit,List.any_map,List.all_eq_true,funext_iff]
  · simp [guardedFormula,CNF.eval,List.all_map,Function.comp_def,LayerRecovery.guard,
      CNF.Clause.eval,extendAssignment,mapLit,List.any_map]

omit [DecidableEq V] in
theorem width_le_four (F : CNF V) (hF : ∀ c ∈ F, c.length ≤ 3) :
    ∀ c ∈ guardedFormula F, c.length ≤ 4 := by
  intro c h
  rcases List.mem_append.mp h with h|h
  · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp h
    have h₀ := hF d hd
    simpa using Nat.succ_le_succ h₀
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
    change 2 ≤ 4
    decide

omit [DecidableEq V] in
theorem all_zero_model (F : CNF V) :
    CNF.Sat (fun _ => false) (guardedFormula F) := by
  rw [CNF.sat_def,show (fun _ : Option V => false) = extendAssignment false (fun _ => false) from
    funext (fun v => by cases v <;> rfl),guardedFormula_eval]
  simp [LayerRecovery.guard]

private def assignmentEquiv : (Bool × (V → Bool)) ≃ (Option V → Bool) where
  toFun p := extendAssignment p.1 p.2
  invFun x := (x none,fun v => x (some v))
  left_inv _ := rfl
  right_inv _ := funext fun v => by cases v <;> rfl

private theorem modelCount_is_sum {W : Type*} [Fintype W] [DecidableEq W] (F : CNF W) :
    PinnedCNF.modelCount F = ∑ x : W → Bool, if F.eval x = true then 1 else 0 := by
  classical
  unfold PinnedCNF.modelCount
  rw [Finset.card_filter]
  apply Finset.sum_congr
  · ext x; simp
  · intro x _; by_cases h : F.eval x = true <;> simp [h]

theorem literal_guarded_count (F : CNF V) :
    PinnedCNF.modelCount (guardedFormula F) = 1+PinnedCNF.modelCount F := by
  classical
  rw [modelCount_is_sum,modelCount_is_sum]
  rw [← Equiv.sum_comp (assignmentEquiv (V := V)),Fintype.sum_prod_type]
  change (∑ z : Bool, ∑ x : V → Bool,
    if (guardedFormula F).eval (extendAssignment z x)=true then 1 else 0) = _
  simp only [guardedFormula_eval]
  exact LayerRecovery.guarded_count F.eval

#print axioms guardedFormula_eval
#print axioms width_le_four
#print axioms all_zero_model
#print axioms literal_guarded_count
end J6Guard
