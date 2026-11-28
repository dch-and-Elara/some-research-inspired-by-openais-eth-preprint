import A1R43LiteralGraph
import J6R11CollisionReindex

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10500000

/-! The exact A2 simulated-incidence collision calculation. Probability
is on independent words for the simulated NAND rows and old equality
columns, before the constant coordinate 0 and physical dummy entries
are installed. This is an existence certificate, not a cost meter. -/
namespace A1R43Literal
open scoped Classical BigOperators
open P11FullPacking J6R10Repack

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V))

def simulated : Network (Occ F) F V := ⟨Prod.fst,endpoint F⟩

omit [Fintype V] [DecidableEq V] in
theorem simulated_row_degree (e : F) : Nat.card {u : Occ F//(simulated F).row u=e}=2 := by
  let eB : {u : Occ F//(simulated F).row u=e} ≃ Bool :=
    { toFun := fun u=>u.val.2
      invFun := fun v=>⟨(e,v),rfl⟩
      left_inv := by intro ⟨⟨q,b⟩,h⟩; cases h; rfl
      right_inv := fun _=>rfl }
  rw [Nat.card_congr eB,Nat.card_eq_fintype_card,Fintype.card_bool]

omit [Fintype V] [DecidableEq V] in
theorem simulated_incidence_count : Nat.card (Occ F)=2*F.card := by
  simp [Occ,Nat.card_eq_fintype_card,Nat.mul_comm]

theorem lower_word_cell_count (a : ℕ) :
    Nat.card (Cell (Fin a) (Fin 64))=J9PrintedSchedule.arrayCard a := by
  rw [total_cells,Fintype.card_fin,J9PrintedSchedule.arrayCard]

theorem A2_chosen_simulation_capacity
    (cubic : ∀ v,GraphCutMoments.degree F v=3) (a Q : ℕ)
    (collision : 2*(J9PrintedSchedule.arrayCard a)^2*3≤Nat.card (Occ F))
    (budget : 2*Nat.card (Occ F)≤Q*J9PrintedSchedule.arrayCard a) :
    ∃ (r : F→Fin a→Fin 64) (c : V→Fin a→Fin 64),
      varianceScore (declaredCell (simulated F) r c)≤2*(Nat.card (Occ F):ℚ)*3 ∧
      ∀ cell, Nat.card (Fiber (declaredCell (simulated F) r c) cell)≤Q := by
  obtain ⟨r,c,hh⟩ := J6R11CollisionReindex.declared_variance_witness (G:=Fin 64) (a:=a)
    (simulated F) 3 (fun e=>by rw [simulated_row_degree]; decide)
    (fun v=>by change Nat.card {u : Occ F//endpoint F u=v}≤3; rw [incidence_card,cubic])
  refine ⟨r,c,hh,?_⟩
  intro cell
  let D := J9PrintedSchedule.arrayCard a
  let m := Nat.card (Occ F)
  have dpos : (0:ℚ)<D := by unfold D J9PrintedSchedule.arrayCard; positivity
  let l := Nat.card (Fiber (declaredCell (simulated F) r c) cell)
  have hsmall : ((l:ℚ)-(m:ℚ)/D)^2≤2*(m:ℚ)*3 := by
    apply le_trans _ hh
    unfold varianceScore
    dsimp only [D]
    rw [← lower_word_cell_count a]
    exact Finset.single_le_sum
      (fun c' _ => sq_nonneg
        ((Nat.card (Fiber (declaredCell (simulated F) r c) c'):ℚ) -
          Nat.card (Occ F)/Nat.card (Cell (Fin a) (Fin 64))))
      (Finset.mem_univ cell)
  have hc : (2:ℚ)*(D:ℚ)^2*3 ≤ m := by exact_mod_cast collision
  have hb : (2:ℚ)*(m:ℚ) ≤ (Q:ℚ)*D := by exact_mod_cast budget
  have hs : 2*(m:ℚ)*3≤ ((m:ℚ)/D)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos dpos _)).2
    calc
      _ = ((2:ℚ)*(D:ℚ)^2*3)*m := by ring
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

#print axioms simulated_row_degree
#print axioms simulated_incidence_count
#print axioms lower_word_cell_count
#print axioms A2_chosen_simulation_capacity
end
end A1R43Literal
