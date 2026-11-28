import F5R60PhysicalClauseBits

/-! Whole logical clause family of printed F1. The switches, edge requests,
three OR-gate clauses and one triple-request clause keep their original signs.
The physical-copy version next replaces each use by a separate occurrence. -/
namespace F5R60
set_option autoImplicit false

structure RequestGraph (V E T : Type) where
  left : E → V
  right : E → V
  first : T → V
  second : T → V
  third : T → V
  available : V → Bool
  edgeActive : E → Bool
  tripleActive : T → Bool

variable {V E T : Type}

def Allowed (G : RequestGraph V E T) (x : V → Bool) : Prop :=
  (∀ v, x v = true → G.available v = true) ∧
  (∀ e, ¬ (x (G.left e) = true ∧ x (G.right e) = true)) ∧
  (∀ e, G.edgeActive e = true → x (G.left e) = true ∨ x (G.right e) = true) ∧
  (∀ t, G.tripleActive t = true →
    x (G.first t) = true ∨ x (G.second t) = true ∨ x (G.third t) = true)

def asY (G : RequestGraph V E T) (x : V → Bool) (t : T) : Bool :=
  x (G.first t) || x (G.second t)

def LogicalPrinted (G : RequestGraph V E T) (x : V → Bool) (y : T → Bool) : Prop :=
  (∀ v, switchClause (G.available v) (x v) = true) ∧
  (∀ e, conflictClause (x (G.left e)) (x (G.right e)) = true) ∧
  (∀ e, edgeClause (G.edgeActive e) (x (G.left e)) (x (G.right e)) = true) ∧
  (∀ t, tripleGate (x (G.first t)) (x (G.second t)) (y t) = true ∧
    tripleClause (G.tripleActive t) (y t) (x (G.third t)) = true)

theorem printed_logical_iff (G : RequestGraph V E T) (x : V → Bool) (y : T → Bool) :
    LogicalPrinted G x y ↔ Allowed G x ∧ ∀ t, y t = asY G x t := by
  constructor
  · rintro ⟨s,e,r,d⟩
    refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
    · intro v
      exact (actual_switch _ _).1 (s v)
    · intro v
      exact (actual_conflict _ _).1 (e v)
    · intro v
      exact (actual_edge_request _ _ _).1 (r v)
    · intro t
      exact (actual_triple_request _ _ _ _ _).1 (d t) |>.2
    · intro t
      exact (actual_triple_request _ _ _ _ _).1 (d t) |>.1
  · rintro ⟨⟨s,e,r,d⟩,yEq⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro v
      exact (actual_switch _ _).2 (s v)
    · intro v
      exact (actual_conflict _ _).2 (e v)
    · intro v
      exact (actual_edge_request _ _ _).2 (r v)
    · intro t
      exact (actual_triple_request _ _ _ _ _).2 ⟨yEq t,d t⟩

theorem logical_extension_unique (G : RequestGraph V E T) (x : V → Bool) :
    Allowed G x ↔ ∃ y, LogicalPrinted G x y ∧ ∀ z, LogicalPrinted G x z → z = y := by
  constructor
  · intro h
    refine ⟨asY G x,(printed_logical_iff G x _).2 ⟨h,fun _ => rfl⟩,?_⟩
    intro z hz
    exact funext ((printed_logical_iff G x z).1 hz).2
  · rintro ⟨y,h,_⟩
    exact ((printed_logical_iff G x y).1 h).1

#print axioms printed_logical_iff
#print axioms logical_extension_unique
end F5R60
