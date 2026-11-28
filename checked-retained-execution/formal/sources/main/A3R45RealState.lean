import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! The unrounded real-rate form of A5 in v9 A3. An internal node has
exactly its *feasible* reply fibres. Any free deterministic processing
is represented inside the next continuation, not as a new reply alphabet. -/
namespace A3R45RealState
open scoped BigOperators
set_option autoImplicit false
set_option warningAsError true

inductive TraceTree (O : Type*) where
  | stop (value : O)
  | read (fee : ℝ) (fibres : ℕ) (next : Fin fibres → TraceTree O)

variable {O : Type*} [DecidableEq O]

def outputs : TraceTree O → Finset O
  | .stop o => {o}
  | .read _ _ next => Finset.univ.biUnion fun i => outputs (next i)

/-- Every feasible terminal path fits the real cost cap, without rounding
its accumulated cost or requiring unreachable replies to be charged. -/
def traceCap : TraceTree O → ℝ → Prop
  | .stop _, T => 0 ≤ T
  | .read fee _ next, T => ∀ j, traceCap (next j) (T - fee)

/-- Bounds the alphabet relative to this exact history, not the size of the
raw representation of one of its replies. -/
def feasibleRate (ρ : ℝ) : TraceTree O → Prop
  | .stop _ => True
  | .read fee n next => 0 ≤ fee ∧ (n : ℝ) ≤ (2 : ℝ) ^ (ρ * fee) ∧
      ∀ j, feasibleRate ρ (next j)

theorem one_state_output_cap (ρ T : ℝ) (hr : 0 ≤ ρ)
    (tree : TraceTree O) (hfit : traceCap tree T) (hallowed : feasibleRate ρ tree) :
    ((outputs tree).card : ℝ) ≤ (2 : ℝ) ^ (ρ * T) := by
  induction tree generalizing T with
  | stop v =>
    have hnonneg : 0 ≤ ρ * T := mul_nonneg hr hfit
    have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) hnonneg
    simpa [outputs] using h
  | read c n next ih =>
    obtain ⟨_, hcount, hnext⟩ := hallowed
    have hs (i : Fin n) := ih i (T-c) (hfit i) (hnext i)
    change ((Finset.univ.biUnion fun j : Fin n => outputs (next j)).card : ℝ) ≤ _
    calc
      _ ≤ ∑ j : Fin n, ((outputs (next j)).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n)))
          (t := fun j => outputs (next j)))
      _ ≤ ∑ _j : Fin n, (2:ℝ) ^ (ρ * (T-c)) := Finset.sum_le_sum fun j _ => hs j
      _ = (n:ℝ) * (2:ℝ) ^ (ρ * (T-c)) := by simp
      _ ≤ (2:ℝ) ^ (ρ*c) * (2:ℝ) ^ (ρ*(T-c)) :=
        mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (by norm_num) _)
      _ = _ := by rw [←Real.rpow_add (by norm_num : 0 < (2:ℝ))]; congr 1; ring

variable {Menu State : Type*}

def allOutputs (menus : Finset Menu) (states : Menu → Finset State)
    (trees : Menu → State → TraceTree O) : Finset O :=
  menus.biUnion fun m => (states m).biUnion fun s => outputs (trees m s)

theorem all_output_cap (menus : Finset Menu) (states : Menu → Finset State)
    (trees : Menu → State → TraceTree O) (B b ρ T : ℝ)
    (hr : 0 ≤ ρ) (hm : (menus.card:ℝ) ≤ (2:ℝ)^B)
    (hs : ∀ m ∈ menus, ((states m).card:ℝ) ≤ (2:ℝ)^b)
    (ht : ∀ m ∈ menus, ∀ s ∈ states m,
      traceCap (trees m s) T ∧ feasibleRate ρ (trees m s)) :
    ((allOutputs menus states trees).card:ℝ) ≤ (2:ℝ)^(B+b+ρ*T) := by
  have hstep m (mm : m ∈ menus) :
      (((states m).biUnion fun s => outputs (trees m s)).card:ℝ) ≤
        (2:ℝ)^b * (2:ℝ)^(ρ*T) := calc
    _ ≤ ∑ s ∈ states m, ((outputs (trees m s)).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := states m) (t := fun s => outputs (trees m s)))
    _ ≤ ∑ _s ∈ states m, (2:ℝ)^(ρ*T) :=
      Finset.sum_le_sum fun s sm =>
        one_state_output_cap ρ T hr (trees m s) (ht m mm s sm).1 (ht m mm s sm).2
    _ = ((states m).card:ℝ) * (2:ℝ)^(ρ*T) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hs m mm) (Real.rpow_nonneg (by norm_num) _)
  unfold allOutputs
  calc
    _ ≤ ∑ m ∈ menus, (((states m).biUnion fun s => outputs (trees m s)).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := menus)
        (t := fun m => (states m).biUnion fun s => outputs (trees m s)))
    _ ≤ ∑ _m ∈ menus, (2:ℝ)^b * (2:ℝ)^(ρ*T) := Finset.sum_le_sum hstep
    _ = (menus.card:ℝ) * ((2:ℝ)^b * (2:ℝ)^(ρ*T)) := by simp
    _ ≤ (2:ℝ)^B * ((2:ℝ)^b * (2:ℝ)^(ρ*T)) :=
      mul_le_mul_of_nonneg_right hm (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _))
    _ = _ := by rw [←mul_assoc, ←Real.rpow_add (by norm_num : 0 < (2:ℝ)),
      ←Real.rpow_add (by norm_num : 0 < (2:ℝ))]

theorem exact_A5_real_rate (menus : Finset Menu) (states : Menu → Finset State)
    (trees : Menu → State → TraceTree O) (targets : Finset O) (B b ρ T : ℝ)
    (hr : 0 < ρ) (hn : targets.Nonempty)
    (hm : (menus.card:ℝ) ≤ (2:ℝ)^B)
    (hs : ∀ m ∈ menus, ((states m).card:ℝ) ≤ (2:ℝ)^b)
    (ht : ∀ m ∈ menus, ∀ s ∈ states m,
      traceCap (trees m s) T ∧ feasibleRate ρ (trees m s))
    (correct : targets ⊆ allOutputs menus states trees) :
    (Real.log (targets.card:ℝ) / Real.log 2 - B - b) / ρ ≤ T := by
  have hc : (targets.card:ℝ) ≤ ((allOutputs menus states trees).card:ℝ) := by
    exact_mod_cast Finset.card_le_card correct
  have hpos : 0 < (targets.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hn
  have H := Real.log_le_log hpos (hc.trans (all_output_cap menus states trees B b ρ T hr.le hm hs ht))
  rw [Real.log_rpow (by norm_num : 0 < (2:ℝ))] at H
  have two : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : Real.log (targets.card:ℝ) / Real.log 2 ≤ B+b+ρ*T := (div_le_iff₀ two).2 (by simpa [mul_comm] using H)
  apply (div_le_iff₀ hr).2
  linarith only [hb]

theorem finite_promise_exact_A5 {X : Type*} [Fintype X] [Nonempty X]
    (menus : Finset Menu) (states : Menu → Finset State)
    (trees : Menu → State → TraceTree O) (menu : X → Menu) (state : X → State)
    (target : X → O) (B b ρ T : ℝ) (hr : 0 < ρ)
    (hm : (menus.card:ℝ) ≤ (2:ℝ)^B)
    (hs : ∀ m ∈ menus, ((states m).card:ℝ) ≤ (2:ℝ)^b)
    (ht : ∀ m ∈ menus, ∀ s ∈ states m,
      traceCap (trees m s) T ∧ feasibleRate ρ (trees m s))
    (realize : ∀ x, menu x ∈ menus ∧ state x ∈ states (menu x) ∧
      target x ∈ outputs (trees (menu x) (state x))) :
    (Real.log ((Finset.univ.image target).card:ℝ) / Real.log 2 - B - b) / ρ ≤ T := by
  apply exact_A5_real_rate menus states trees (Finset.univ.image target) B b ρ T hr
  · rcases ‹Nonempty X› with ⟨x⟩
    exact ⟨target x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  · exact hm
  · exact hs
  · exact ht
  · intro o ho
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ho
    obtain ⟨hx, hy, hz⟩ := realize x
    exact Finset.mem_biUnion.mpr ⟨menu x, hx,
      Finset.mem_biUnion.mpr ⟨state x, hy, hz⟩⟩

#print axioms one_state_output_cap
#print axioms all_output_cap
#print axioms exact_A5_real_rate
#print axioms finite_promise_exact_A5
end A3R45RealState
