import F5R60OccurrenceCycle
import F5R60LogicalRequests

/-! Physical source slots are assigned before literal signs are applied.
The clauses below use exactly the printed F1 positions. Legal cycle orders
are data; constructing a canonical order avoiding the forbidden within-clause
adjacencies, and the external F5 ambient construction, are separate. -/
namespace F5R60
set_option autoImplicit false
variable {V E T : Type}

inductive PrivatePos (V E T : Type)
  | sw (v : V) (i : Fin 2)
  | cf (e : E) (i : Fin 2)
  | er (e : E) (i : Fin 3)
  | tr (t : T) (i : Fin 10)

abbrev Logical (V T : Type) := Sum V T

def nameOf (G : RequestGraph V E T) : PrivatePos V E T → Logical V T
  | .sw v _ => .inl v
  | .cf e i => if i.val = 0 then .inl (G.left e) else .inl (G.right e)
  | .er e i => if i.val = 1 then .inl (G.right e) else .inl (G.left e)
  | .tr t i =>
    if i.val = 0 ∨ i.val = 4 then .inl (G.first t)
    else if i.val = 2 ∨ i.val = 5 then .inl (G.second t)
    else if i.val = 8 ∨ i.val = 9 then .inl (G.third t)
    else .inr t

structure PrintedCycles (G : RequestGraph V E T) where
  first : Logical V T → PrivatePos V E T
  rest : Logical V T → List (PrivatePos V E T)
  last : Logical V T → PrivatePos V E T
  firstName : ∀ n, nameOf G (first n) = n
  lastName : ∀ n, nameOf G (last n) = n
  restName : ∀ n p, p ∈ rest n → nameOf G p = n
  covered : ∀ p, p ∈ first (nameOf G p) :: rest (nameOf G p)
  chainOrder : ∀ n, Chain (fun (_ : PrivatePos V E T) => false) (first n) (rest n) (last n)

def restrictBits (G : RequestGraph V E T) (v : Logical V T → Bool) :
    PrivatePos V E T → Bool := fun pos => v (nameOf G pos)

def logicalBits (x : V → Bool) (y : T → Bool) : Logical V T → Bool
  | .inl v => x v
  | .inr t => y t

def BasePositions (G : RequestGraph V E T) (b : PrivatePos V E T → Bool) : Prop :=
  (∀ v, ((!b (.sw v 0)) || literalBit (G.available v) (b (.sw v 1))) = true) ∧
  (∀ e, ((!b (.cf e 0)) || (!b (.cf e 1))) = true) ∧
  (∀ e, (b (.er e 0) || b (.er e 1) || literalBit (G.edgeActive e) (b (.er e 2))) = true) ∧
  (∀ t, ((!b (.tr t 0)) || b (.tr t 1)) = true ∧
    ((!b (.tr t 2)) || b (.tr t 3)) = true ∧
    (b (.tr t 4) || b (.tr t 5) || (!b (.tr t 6))) = true ∧
    (b (.tr t 7) || b (.tr t 8) || literalBit (G.tripleActive t) (b (.tr t 9))) = true)

def PhysicalPrinted (G : RequestGraph V E T) (D : PrintedCycles G)
    (b : PrivatePos V E T → Bool) (detached : Bool × Bool) : Prop :=
  BasePositions G b ∧
    (∀ n, ClosedCycle b (D.first n) (D.rest n) (D.last n)) ∧
    (detached.1 || detached.2) = true

theorem actual_positions_reduce (G : RequestGraph V E T) (x : V → Bool) (y : T → Bool) :
    BasePositions G (restrictBits G (logicalBits x y)) ↔ LogicalPrinted G x y := by
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  simp only [restrictBits,nameOf,logicalBits]
  constructor
  · rintro ⟨sw,cf,er,tr⟩
    exact ⟨sw,cf,er,fun t => by
      rcases tr t with ⟨a,b,c,d⟩
      exact ⟨Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨a,b⟩,c⟩,d⟩⟩
  · rintro ⟨sw,cf,er,tr⟩
    exact ⟨sw,cf,er,fun t => by
      rcases tr t with ⟨abc,d⟩
      have ab_c := Bool.and_eq_true_iff.1 abc
      have a_b := Bool.and_eq_true_iff.1 ab_c.1
      exact ⟨a_b.1,a_b.2,ab_c.2,d⟩⟩

theorem printed_cycle_copyback (G : RequestGraph V E T) (D : PrintedCycles G)
    (b : PrivatePos V E T → Bool)
    (h : ∀ n, ClosedCycle b (D.first n) (D.rest n) (D.last n)) :
    b = restrictBits G (logicalBits (fun v => b (D.first (.inl v))) (fun t => b (D.first (.inr t)))) := by
  funext pos
  have eq := actual_cycle_forces_equal b (D.rest (nameOf G pos)) (h (nameOf G pos)) (D.covered pos)
  cases ename : nameOf G pos with
  | inl v =>
    change b pos = logicalBits _ _ (nameOf G pos)
    rw [ename] at eq ⊢
    exact eq
  | inr t =>
    change b pos = logicalBits _ _ (nameOf G pos)
    rw [ename] at eq ⊢
    exact eq

theorem lift_chain {A : Type} (a : A → Bool) (as : List A) {x y : A}
    (h : Chain (fun (_ : A) => false) x as y)
    (mono : ∀ z, z ∈ x::as → a z = a x) :
    Chain a x as y := by
  induction as generalizing x with
  | nil => exact h
  | cons z zs ih =>
    have zb := mono z (List.mem_cons_of_mem _ List.mem_cons_self)
    refine ⟨fun v => zb.trans v,?_⟩
    exact ih h.2 (fun t ht => (mono t (List.mem_cons_of_mem _ ht)).trans zb.symm)

theorem actual_F1_sat_iff_allowed (G : RequestGraph V E T) (D : PrintedCycles G) :
    (∃ b detached, PhysicalPrinted G D b detached) ↔ ∃ x, Allowed G x := by
  constructor
  · rintro ⟨b,d,base,cyc,_⟩
    let x : V → Bool := fun v => b (D.first (.inl v))
    let y : T → Bool := fun t => b (D.first (.inr t))
    have eq : b = restrictBits G (logicalBits x y) := printed_cycle_copyback G D b cyc
    rw [eq] at base
    exact ⟨x,((printed_logical_iff G x y).1 ((actual_positions_reduce G x y).1 base)).1⟩
  · rintro ⟨x,h⟩
    let y := asY G x
    let b := restrictBits G (logicalBits x y)
    refine ⟨b,(true,false),(actual_positions_reduce G x y).2 ((printed_logical_iff G x y).2 ⟨h,fun _=>rfl⟩),?_,rfl⟩
    intro n
    have atFirst : b (D.first n) = logicalBits x y n := congrArg (logicalBits x y) (D.firstName n)
    have atLast : b (D.last n) = logicalBits x y n := congrArg (logicalBits x y) (D.lastName n)
    refine ⟨lift_chain b _ (D.chainOrder n) ?_,fun v => (atFirst.trans atLast.symm).trans v⟩
    intro z mem
    rcases List.mem_cons.mp mem with e | earlier
    · simp [e]
    · exact (congrArg (logicalBits x y) (D.restName n z earlier)).trans atFirst.symm

#print axioms actual_positions_reduce
#print axioms printed_cycle_copyback
#print axioms lift_chain
#print axioms actual_F1_sat_iff_allowed
end F5R60

