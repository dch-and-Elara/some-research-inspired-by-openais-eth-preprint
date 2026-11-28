import A1R43LiteralGenericLayout
import A1R43LiteralEstimate
import A1R43LiteralSchedule

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 11600000

/-! A2 uses the same root layout with arity at most four (or six for the
literal paired #3SAT variant). Derive the common capacity from the
original root guards; do not alter native source size or geometry. -/
namespace A1R43Literal.General
open scoped Classical Polynomial BigOperators
open P11FullPacking J6R10Repack J1PPrinted
noncomputable section

theorem collision_for_real_degree (m k : ℕ) (guard : PrintedMargins m)
    (hk : k≤sourceDelta (starSize m)) :
    2*(J9PrintedSchedule.arrayCard (smallA m))^2*k≤m := by
  have src := (source_packing_conditions (starSize m) (half m) 0 guard.u_pos guard.active_half).1
  rw [source_D_zero] at src
  have hd : fullCells m=4096*J9PrintedSchedule.arrayCard (smallA m) := by
    unfold fullCells J9PrintedSchedule.arrayCard
    rw [←guard.full_dim,show 2*(smallA m+1)=2*smallA m+2 by omega,pow_add]
    ring
  have hb := (Nat.mul_le_mul_left (2*(fullCells m)^2) hk).trans src
  rw [hd,source_half] at hb
  have same : 2*(4096*J9PrintedSchedule.arrayCard (smallA m))^2*k =
      16777216*(2*(J9PrintedSchedule.arrayCard (smallA m))^2*k) := by ring
  rw [same] at hb
  omega

theorem source_delta_ge_six (m : ℕ) (guard : PrintedMargins m) :
    6≤sourceDelta (starSize m) := by
  have bound := (source_packing_conditions (starSize m) (half m) 0 guard.u_pos guard.active_half).2.2
  rw [source_L_zero] at bound
  have hp : 4≤lengthL m := by
    unfold lengthL nativeA J9PrintedSchedule.rootA
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 2≤2*J9PrintedSchedule.rootU (Nat.clog 2 (starSize m)) by
      have h := guard.u_pos
      omega)
  omega

variable {U A B : Type} [Fintype U] [Fintype A] [Fintype B]

theorem chosen_simulation_capacity (T : Network U A B) (a Q k : ℕ)
    (hA : ∀ r, Nat.card {u : U // T.row u=r}≤k)
    (hB : ∀ c, Nat.card {u : U // T.col u=c}≤k)
    (collision : 2*(J9PrintedSchedule.arrayCard a)^2*k≤Nat.card U)
    (budget : 2*Nat.card U≤Q*J9PrintedSchedule.arrayCard a) :
    ∃ (r : A→Fin a→Fin 64) (c : B→Fin a→Fin 64),
      varianceScore (declaredCell T r c)≤2*(Nat.card U:ℚ)*k ∧
      ∀ cell, Nat.card (Fiber (declaredCell T r c) cell)≤Q := by
  obtain ⟨r,c,hh⟩ := J6R11CollisionReindex.declared_variance_witness (G:=Fin 64) (a:=a)
    T k hA hB
  refine ⟨r,c,hh,?_⟩
  intro cell
  let D := J9PrintedSchedule.arrayCard a
  let m := Nat.card U
  have dpos : (0:ℚ)<D := by unfold D J9PrintedSchedule.arrayCard; positivity
  let l := Nat.card (Fiber (declaredCell T r c) cell)
  have hsmall : ((l:ℚ)-(m:ℚ)/D)^2≤2*(m:ℚ)*k := by
    apply le_trans _ hh
    unfold varianceScore
    dsimp only [D]
    rw [← lower_word_cell_count a]
    exact Finset.single_le_sum
      (fun c' _ => sq_nonneg
        ((Nat.card (Fiber (declaredCell T r c) c'):ℚ) -
          Nat.card U/Nat.card (Cell (Fin a) (Fin 64))))
      (Finset.mem_univ cell)
  have hc : (2:ℚ)*(D:ℚ)^2*k ≤ m := by exact_mod_cast collision
  have hb : (2:ℚ)*(m:ℚ) ≤ (Q:ℚ)*D := by exact_mod_cast budget
  have hs : 2*(m:ℚ)*k≤ ((m:ℚ)/D)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos dpos _)).2
    calc
      _ = ((2:ℚ)*(D:ℚ)^2*k)*m := by ring
      _ ≤ (m:ℚ)*m := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hl : (l:ℚ)≤(2:ℚ)*(m:ℚ)/D := by
    by_contra hh'
    push_neg at hh'
    have hn0 : (0:ℚ)≤(2:ℚ)*(m:ℚ)/D := by positivity
    have hn : 0<(l:ℚ) := hn0.trans_lt hh'
    have hg : 0 < (l:ℚ) - 2*((m:ℚ)/D) :=
      sub_pos.mpr (by simpa only [mul_div_assoc] using hh')
    nlinarith [hsmall.trans hs,mul_pos hn hg]
  have hq : (2:ℚ)*(m:ℚ)/D ≤ Q := (div_le_iff₀ dpos).2 hb
  exact_mod_cast hl.trans hq


theorem printed_general_pair_plan (T : Network U A B) (k : ℕ)
    (guard : PrintedMargins (Nat.card U)) (hk : k≤6)
    (hA : ∀ r,Nat.card {u : U//T.row u=r}≤k)
    (hB : ∀ c,Nat.card {u : U//T.col u=c}≤k) :
    Nonempty (PairPlan T (smallA (Nat.card U)) (copies (Nat.card U))) := by
  obtain ⟨r,c,_h,cap⟩ := chosen_simulation_capacity T (smallA (Nat.card U))
    (copies (Nat.card U)*2^smallA (Nat.card U)) k hA hB
    (collision_for_real_degree _ k guard (hk.trans (source_delta_ge_six _ guard)))
    guard.paired_capacity
  exact ⟨⟨0,r,c,cap⟩⟩

#print axioms collision_for_real_degree
#print axioms source_delta_ge_six
#print axioms chosen_simulation_capacity
#print axioms printed_general_pair_plan
end
end A1R43Literal.General
