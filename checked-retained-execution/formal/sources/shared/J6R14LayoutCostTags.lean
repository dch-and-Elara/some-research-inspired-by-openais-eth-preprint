import J6R14LayoutCostGroup

/-! Tag each edge occurrence before grouping. Equal incidence values of
distinct parallel edges therefore remain distinct after serialization.
A ripple word supplies each identifier; no random-access edge
enumeration is part of the executable loop. -/

namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionEdges J6R12CollisionMenu

structure Tagged where
  serial : List Bool
  edge : EdgeTape

def tagStepCap (kR kC b q : ℕ) : ℕ :=
  12*q+recordTraffic kR kC b q

def serialTags (kR kC b q : ℕ) : List Bool → List EdgeTape → Meter (List Tagged)
  | _,[] => ⟨[],0⟩
  | word,e::es =>
    let v := addBits word (encodeBits q 1)
    let s := serialTags kR kC b q v.result es
    ⟨⟨word,e⟩::s.result,v.steps+s.steps+recordTraffic kR kC b q⟩

def tagSpec (q : ℕ) : ℕ → List EdgeTape → List Tagged
  | _,[] => []
  | j,e::es => ⟨encodeBits q j,e⟩::tagSpec q (j+1) es

theorem tagSpec_edge (q j : ℕ) (es : List EdgeTape) :
    (tagSpec q j es).map Tagged.edge=es := by
  induction es generalizing j with
  | nil => rfl
  | cons e es ih => simp [tagSpec,ih]

theorem tagSpec_length (q j : ℕ) (es : List EdgeTape) :
    (tagSpec q j es).length=es.length := by
  induction es generalizing j with
  | nil => rfl
  | cons e es ih => simp [tagSpec,ih]

theorem tagSpec_at (q j : ℕ) (es : List EdgeTape) (k : ℕ) :
    (tagSpec q j es)[k]?=es[k]?.map (fun e => ⟨encodeBits q (j+k),e⟩) := by
  induction es generalizing j k with
  | nil => simp [tagSpec]
  | cons e es ih =>
    cases k with
    | zero => simp [tagSpec]
    | succ k =>
      simpa [tagSpec, Nat.succ_eq_add_one, Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using (ih (j+1) k)

theorem serialTags_exact (kR kC b q : ℕ) (hq : 0<q) (j : ℕ) (es : List EdgeTape)
    (h : j+es.length<2^q) :
    let s := serialTags kR kC b q (encodeBits q j) es
    s.result=tagSpec q j es ∧ s.steps≤es.length*tagStepCap kR kC b q := by
  induction es generalizing j with
  | nil => simp [serialTags,tagSpec]
  | cons e es ih =>
    have hk : j+1+es.length<2^q := by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
    have hj : j<2^q := by omega
    have hj' : j+1<2^q := by omega
    have h1 : 1<(2:ℕ)^q := one_lt_pow₀ (by decide) hq.ne'
    let v := addBits (encodeBits q j) (encodeBits q 1)
    obtain ⟨hl,hv,hs⟩ := addBits_exact (encodeBits q j) (encodeBits q 1)
      ((encodeBits_length _ _).trans (encodeBits_length _ _).symm)
    have H : v.result=encodeBits q (j+1) := by
      apply equal_width_inj
      · change (addBits (encodeBits q j) (encodeBits q 1)).result.length=_
        rw [hl,encodeBits_length,encodeBits_length]
      · change bitsValue (addBits (encodeBits q j) (encodeBits q 1)).result=_
        rw [hv,encodeBits_exact _ _ hj,encodeBits_exact _ _ h1,encodeBits_length,
          Nat.mod_eq_of_lt hj',encodeBits_exact _ _ hj']
    obtain ⟨hR,hC⟩ := ih (j+1) hk
    refine ⟨?_,?_⟩
    · change (Tagged.mk (encodeBits q j) e :: (serialTags kR kC b q v.result es).result)=_
      rw [H,hR]
      rfl
    · change v.steps+(serialTags kR kC b q v.result es).steps+recordTraffic kR kC b q≤_
      rw [H,show v.steps=_ from hs,encodeBits_length,List.length_cons,Nat.succ_mul es.length]
      unfold tagStepCap at hC ⊢
      omega

def tagAll (kR kC b q : ℕ) (es : List EdgeTape) : Meter (List Tagged) :=
  let t := serialTags kR kC b q (encodeBits q 0) es
  ⟨t.result,t.steps+q+2⟩

theorem tagAll_exact (kR kC b q : ℕ) (hq : 0<q) (es : List EdgeTape) (h : es.length<2^q) :
    (tagAll kR kC b q es).result=tagSpec q 0 es ∧
      (tagAll kR kC b q es).steps≤es.length*tagStepCap kR kC b q+q+2 := by
  obtain ⟨hr,hc⟩ := serialTags_exact kR kC b q hq 0 es (by simpa using h)
  exact ⟨hr,Nat.add_le_add_right (Nat.add_le_add_right hc _) _⟩

#print axioms tagSpec_at
#print axioms serialTags_exact
#print axioms tagAll_exact
end J6R14LayoutCost

