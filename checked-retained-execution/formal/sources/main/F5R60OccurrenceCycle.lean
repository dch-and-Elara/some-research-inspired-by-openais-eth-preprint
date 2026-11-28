import Init

/-! A directed occurrence cycle enforces the original shared logical bit.
The list describes the actual cyclic order of distinct physical positions;
repeat logical names are not identified by changing the physical variables. -/
namespace F5R60
set_option autoImplicit false

def Imp (u v : Bool) : Prop := u = true → v = true

def Chain {A : Type} (b : A → Bool) : A → List A → A → Prop
  | x, [], y => x = y
  | x, z :: rest, y => Imp (b x) (b z) ∧ Chain b z rest y

theorem chain_back {A : Type} (b : A → Bool) (xs : List A) {x y : A}
    (h : Chain b x xs y) : Imp (b x) (b y) := by
  induction xs generalizing x with
  | nil =>
    change x = y at h
    subst y
    exact fun q => q
  | cons z rest ih =>
    exact fun q => ih h.2 (h.1 q)

theorem chain_between {A : Type} (b : A → Bool) (xs : List A) {x y z : A}
    (h : Chain b x xs y) (m : z ∈ xs) : Imp (b x) (b z) ∧ Imp (b z) (b y) := by
  induction xs generalizing x with
  | nil => simp at m
  | cons a rest ih =>
    rcases List.mem_cons.mp m with eq | later
    · subst z
      exact ⟨h.1,chain_back b rest h.2⟩
    · obtain ⟨left,right⟩ := ih h.2 later
      exact ⟨fun q => left (h.1 q),right⟩

def ClosedCycle {A : Type} (b : A → Bool) (first : A) (rest : List A) (last : A) : Prop :=
  Chain b first rest last ∧ Imp (b last) (b first)

theorem actual_cycle_forces_equal {A : Type} (b : A → Bool) {x y z : A} (xs : List A)
    (h : ClosedCycle b x xs y) (m : z ∈ x :: xs) : b z = b x := by
  rcases List.mem_cons.mp m with e | m
  · subst z
    rfl
  obtain ⟨left,right⟩ := chain_between b xs h.1 m
  cases hx : b x <;> cases hz : b z
  · rfl
  · have bad := h.2 (right hz)
    rw [hx] at bad
    contradiction
  · have bad := left hx
    rw [hz] at bad
    contradiction
  · rfl

theorem chain_from_equal {A : Type} (b : A → Bool) (xs : List A) (x : A) :
    (∀ z ∈ xs, b z = b x) → ∃ y, Chain b x xs y ∧ b y = b x := by
  induction xs generalizing x with
  | nil => intro _; exact ⟨x,rfl,rfl⟩
  | cons z rest ih =>
    intro h
    have e := h z List.mem_cons_self
    obtain ⟨y, step, last⟩ := ih z (fun w mw => (h w (List.mem_cons_of_mem _ mw)).trans e.symm)
    exact ⟨y,⟨fun q => e.trans q,step⟩,last.trans e⟩

theorem equal_copies_satisfy_actual_cycle {A : Type} (b : A → Bool) (x : A) (xs : List A) :
    (∀ z ∈ xs, b z = b x) → ∃ y, ClosedCycle b x xs y := by
  intro h
  obtain ⟨y,f,e⟩ := chain_from_equal b xs x h
  exact ⟨y,f,fun q => e.symm.trans q⟩

#print axioms chain_back
#print axioms chain_between
#print axioms actual_cycle_forces_equal
#print axioms chain_from_equal
#print axioms equal_copies_satisfy_actual_cycle
end F5R60
