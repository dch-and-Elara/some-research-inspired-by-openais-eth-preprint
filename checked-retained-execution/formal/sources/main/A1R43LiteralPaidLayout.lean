import A1R43LiteralGeneralEstimate
import J6R12CollisionSource

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 16500000
set_option maxRecDepth 1900

/-! Consume the source's actual metered conditional-expectation words,
then use those very words in the cold-coordinate paired installation.
The input is the explicit endpoint and vertex tapes of the simulated
graph. This prices its label selection, not graph parsing or the later
physical slot/filler tape serialization. -/
namespace A1R43Literal.General
open scoped Classical BigOperators
open P11FullPacking J6R10Repack J6R11Collision J6R11CollisionReindex
open J6R12CollisionGreedyStep J6R12CollisionSource J6R12CollisionRun J6R11CollisionGreedy
noncomputable section

variable {U A B : Type} [Fintype U] [Fintype A] [Fintype B]
variable (T : Network U A B)

omit [Fintype U] [Fintype A] [Fintype B] in
theorem cap_from_real_deviation (a Q k : ℕ) (r : A→Fin a→Fin 64) (c : B→Fin a→Fin 64)
    (collision : 2*(J9PrintedSchedule.arrayCard a)^2*k≤Nat.card U)
    (budget : 2*Nat.card U≤Q*J9PrintedSchedule.arrayCard a)
    (hh : varianceScore (declaredCell T r c)≤2*(Nat.card U:ℚ)*k) :
    ∀ cell,Nat.card (Fiber (declaredCell T r c) cell)≤Q := by
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


open AOracleMachineTime
variable {a : ℕ}

theorem exact_chosen_labels_feed_actual_pair_plan (m : ℕ) (hm : m=Nat.card U)
    (a_eq : a=smallA m) (guard : PrintedMargins m)
    (F : Format U A B (Fin a→Fin 64)) (hrow : F.row=T.row) (hcol : F.col=T.col)
    (hb : F.b=6*a) (vs : List (A⊕B)) (hn : vs.Nodup) (hv : ∀ i,i∈vs)
    (k : ℕ) (hk : k≤6)
    (hA : ∀ r,Nat.card {u : U//T.row u=r}≤k)
    (hB : ∀ c,Nat.card {u : U//T.col u=c}≤k) :
    let out := drive F.e F.kR F.kC F.b (vs.map F.target) (F.graph (fun _=>none))
    ∃ (z : A⊕B→Fin a→Fin 64) (W : PairPlan T a (copies m)),
      W.row=(fun r=>z (.inl r)) ∧ W.col=(fun c=>z (.inr c)) ∧
      out.result.1=F.graph (fun i=>some (z i)) ∧
      out.result.2=vs.map (fun i=>F.label (z i)) ∧
      out.steps≤(F.stepBound (2^(6*a))+2*F.b+6)*(Fintype.card A+Fintype.card B) +
        16*(F.b+1)*2^(6*a)+12*F.width+20 ∧
      ∀ u, ((fullPacking T W).seat (oddWire U (Spare T W) u)).1 =
          ((fullPacking T W).seat (evenWire U (Spare T W) u)).1 ∧
        ((fullPacking T W).seat (evenWire U (Spare T W) u)).2.val+1 =
          ((fullPacking T W).seat (oddWire U (Spare T W) u)).2.val := by
  dsimp only
  have hr (v : A) : (fibre F.row v).card≤k := by
    rw [card_filter_fibre,hrow]
    exact hA v
  have hc (v : B) : (fibre F.col v).card≤k := by
    rw [card_filter_fibre,hcol]
    exact hB v
  obtain ⟨z,tape,words,hdev,paid⟩ := source_64 a (Fintype.card_fin 64) F hb vs hn hv k hr hc
  let r : A→Fin a→Fin 64 := fun v=>z (.inl v)
  let c : B→Fin a→Fin 64 := fun v=>z (.inr v)
  have hd : varianceScore (declaredCell T r c)≤2*(Nat.card U:ℚ)*k := by
    rw [Nat.card_eq_fintype_card]
    have eq := J6R11CollisionReindex.declared_variance_eq T (splitSample z)
    change varianceScore (declaredCell T r c)=_ at eq
    rw [eq,←hrow,←hcol]
    exact hdev
  have hcoll : 2*(J9PrintedSchedule.arrayCard a)^2*k≤Nat.card U := by
    rw [a_eq,←hm]
    exact collision_for_real_degree m k guard (hk.trans (source_delta_ge_six m guard))
  have hslots : 2*Nat.card U≤(copies m*2^a)*J9PrintedSchedule.arrayCard a := by
    rw [a_eq,←hm]
    exact guard.paired_capacity
  let cap := cap_from_real_deviation T a (copies m*2^a) k r c hcoll hslots hd
  let W : PairPlan T a (copies m) := ⟨0,r,c,cap⟩
  exact ⟨z,W,rfl,rfl,tape,words,paid,full_seat_predecessor T W⟩

#print axioms cap_from_real_deviation
#print axioms exact_chosen_labels_feed_actual_pair_plan
end
end A1R43Literal.General
