import V8PooledRangeOrigin
import Mathlib.Data.ZMod.Basic

/-! C2 actual input chart: turn off all switches not belonging to a
specified induced matching. Each endpoint is a real vertex of the
same graph and the actual five-copy count is used below. -/
namespace V8NativeMessage
open scoped Classical BigOperators
open V8PooledRange V8PooledRange.NativeOrigin

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1900000

variable {V E : Type*} {m : ℕ}

structure Pairs (G : Graph V E) (m : ℕ) where
  seat : (Fin m × Bool) ↪ V
  edge : Fin m → E
  reverse : Fin m → Bool
  left : ∀ j, G (edge j) (reverse j)=seat (j,false)
  right : ∀ j, G (edge j) (!(reverse j))=seat (j,true)
  only : ∀ e x y, G e false=seat x → G e true=seat y → x.1=y.1 ∧ x.2≠y.2

variable {G : Graph V E} (K : Pairs G m)

def liftPairs (bits : Fin m × Bool → Bool) (v : V) : Bool :=
  if h : v∈Set.range K.seat then bits (Classical.choose h) else false

theorem liftPairs_on (bits : Fin m × Bool → Bool) (j : Fin m × Bool) :
    liftPairs K bits (K.seat j)=bits j := by
  have h : K.seat j∈Set.range K.seat := ⟨j,rfl⟩
  have hj : Classical.choose h=j := K.seat.injective (Classical.choose_spec h)
  simp only [liftPairs,dif_pos h,hj]

theorem liftPairs_off (bits : Fin m × Bool → Bool) (v : V) (h : v∉Set.range K.seat) :
    liftPairs K bits v=false := dif_neg h

def activeSigns (x y : Fin m → Bool) : V → Bool :=
  liftPairs K (fun j => if j.2 then y j.1 else x j.1)

theorem activeSigns_left (x y : Fin m → Bool) (j : Fin m) :
    activeSigns K x y (K.seat (j,false))=x j :=
  liftPairs_on K _ (j,false)

theorem activeSigns_right (x y : Fin m → Bool) (j : Fin m) :
    activeSigns K x y (K.seat (j,true))=y j :=
  liftPairs_on K _ (j,true)

def pairAllows (x y : Bool) (v : Bool × Bool) : Prop :=
  (v.1=false ∨ x=true) ∧ (v.2=false ∨ y=true) ∧ (v.1=false ∨ v.2=false)

instance (x y : Bool) : DecidablePred (pairAllows x y) :=
  fun v => by unfold pairAllows; infer_instance

abbrev PairStates (x y : Bool) := {v : Bool × Bool // pairAllows x y v}

def enabledPair (a : Bool) : ℕ := if a then 1 else 0

theorem localCount (x y : Bool) :
    Fintype.card (PairStates x y)=1+enabledPair x+enabledPair y := by
  cases x <;> cases y <;> decide

theorem pair_allowed_iff (x y : Fin m → Bool) (s : V → Bool) :
    allowed G (activeSigns K x y) s ↔
      (∀ v, v∉Set.range K.seat → s v=false) ∧
      (∀ j, pairAllows (x j) (y j) (s (K.seat (j,false)), s (K.seat (j,true)))) := by
  constructor
  · intro h
    refine ⟨fun v hv => ?_,fun j => ?_⟩
    · exact (h.1 v).resolve_right (by rw [activeSigns,liftPairs_off K _ v hv]; decide)
    · refine ⟨?_,?_,?_⟩
      · simpa only [activeSigns_left] using h.1 (K.seat (j,false))
      · simpa only [activeSigns_right] using h.1 (K.seat (j,true))
      · have hE := h.2 (K.edge j)
        have hl := K.left j
        have hr := K.right j
        cases hR : K.reverse j
        · simp only [hR,Bool.not_false] at hl hr
          rwa [hl,hr] at hE
        · simp only [hR,Bool.not_true] at hl hr
          rw [hr,hl] at hE
          exact hE.symm
  · rintro ⟨ho,h⟩
    constructor
    · intro v
      by_cases hv : v∈Set.range K.seat
      · obtain ⟨⟨j,b⟩,rfl⟩ := hv
        cases b
        · rw [activeSigns_left]
          exact (h j).1
        · rw [activeSigns_right]
          exact (h j).2.1
      · exact Or.inl (ho v hv)
    · intro e
      by_cases hf : G e false∈Set.range K.seat
      · by_cases ht : G e true∈Set.range K.seat
        · obtain ⟨⟨i,a⟩,ha⟩ := hf
          obtain ⟨⟨j,b⟩,hb⟩ := ht
          have h₁ := K.only e (i,a) (j,b) ha.symm hb.symm
          obtain ⟨hij,hab⟩ := h₁
          change i=j at hij
          subst j
          rw [← ha,← hb]
          cases a <;> cases b
          · exact False.elim (hab rfl)
          · exact (h i).2.2
          · exact (h i).2.2.symm
          · exact False.elim (hab rfl)
        · exact Or.inr (ho _ ht)
      · exact Or.inl (ho _ hf)

def independentPairs (x y : Fin m → Bool) :
    Independent G (activeSigns K x y) ≃ ((j : Fin m) → PairStates (x j) (y j)) where
  toFun s j := ⟨(s.val (K.seat (j,false)),s.val (K.seat (j,true))),
    ((pair_allowed_iff K x y s.val).mp s.property).2 j⟩
  invFun f :=
    let s := liftPairs K (fun j => if j.2 then (f j.1).val.2 else (f j.1).val.1)
    ⟨s,(pair_allowed_iff K x y s).mpr
      ⟨fun v hv => liftPairs_off K _ v hv,fun j => by
        unfold s
        rw [liftPairs_on K _ (j,false),liftPairs_on K _ (j,true)]
        exact (f j).property⟩⟩
  left_inv s := by
    apply Subtype.ext
    funext v
    by_cases h : v∈Set.range K.seat
    · obtain ⟨j,rfl⟩ := h
      change liftPairs K (fun j => if j.2 then s.val (K.seat (j.1,true))
        else s.val (K.seat (j.1,false))) (K.seat j)=s.val (K.seat j)
      rw [liftPairs_on]
      rcases j with ⟨n,b⟩
      cases b <;> rfl
    · change liftPairs K (fun j => if j.2 then s.val (K.seat (j.1,true))
        else s.val (K.seat (j.1,false))) v=s.val v
      exact (liftPairs_off K _ v h).trans (((pair_allowed_iff K x y s.val).mp s.property).1 v h).symm
  right_inv f := by
    funext j
    apply Subtype.ext
    apply Prod.ext
    · change liftPairs K (fun k => if k.2 then (f k.1).val.2 else (f k.1).val.1)
        (K.seat (j,false))=(f j).val.1
      exact liftPairs_on K _ (j,false)
    · change liftPairs K (fun k => if k.2 then (f k.1).val.2 else (f k.1).val.1)
        (K.seat (j,true))=(f j).val.2
      exact liftPairs_on K _ (j,true)

variable [Fintype V] [Fintype E]

theorem C2_count (p : ThreePorts G) (x y : Fin m → Bool) :
    originCount G p (activeSigns K x y) =
      3*∏ j : Fin m, (1+enabledPair (x j)+enabledPair (y j)) := by
  rw [originCount_eq,five_copy_count,Fintype.card_congr (independentPairs K x y),Fintype.card_pi]
  simp only [localCount]

theorem local_parity (x y : Bool) :
    ((1+enabledPair x+enabledPair y:ℕ):ZMod 2)=(if x=y then 1 else 0) := by
  cases x <;> cases y <;> decide

/-- The true origin count on C2 has the identity parity rows. -/
theorem C2_parity (p : ThreePorts G) (x y : Fin m → Bool) :
    (originCount G p (activeSigns K x y):ZMod 2)=(if x=y then 1 else 0) := by
  rw [C2_count]
  simp only [Nat.cast_mul,Nat.cast_prod,local_parity]
  have h3 : (↑(3:ℕ):ZMod 2)=1 := by decide
  rw [h3,one_mul]
  by_cases h : x=y
  · subst y
    simp
  · rw [if_neg h]
    have ht : ∃ j, x j≠y j := by
      by_contra! he
      exact h (funext he)
    obtain ⟨j,hj⟩ := ht
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

#print axioms liftPairs_on
#print axioms pair_allowed_iff
#print axioms independentPairs
#print axioms C2_count
#print axioms C2_parity
end
end V8NativeMessage
