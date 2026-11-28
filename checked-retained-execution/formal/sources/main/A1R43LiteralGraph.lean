import GraphCutMoments
import J6R10RepackPrecision

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000

/-! A1's physical root: each simulated incidence is split into one
column-side wire and one row-side wire. They share neither endpoint.
Real centres see only unary neighbours, so the physical graph is a
disjoint union of stars independently of where these wires are seated. -/
namespace A1R43Literal
open scoped BigOperators
open J6R10Repack

variable {V : Type} [DecidableEq V] (F : Finset (V × V)) (Pad : Type)

abbrev Occ := F × Bool
abbrev Wire := (Occ F × Bool) ⊕ Pad
abbrev Row := F ⊕ (Occ F ⊕ Pad)
abbrev Col := V ⊕ (Occ F ⊕ Pad)

def endpoint (u : Occ F) : V := if u.2 then u.1.val.2 else u.1.val.1

def network : Network (Wire F Pad) (Row F Pad) (Col F Pad) where
  row
    | .inl (u,false) => .inr (.inl u)
    | .inl (u,true) => .inl u.1
    | .inr z => .inr (.inr z)
  col
    | .inl (u,false) => .inl (endpoint F u)
    | .inl (u,true) => .inr (.inl u)
    | .inr z => .inr (.inr z)

local notation "N" => network F Pad

def evenWire (u : Occ F) : Wire F Pad := .inl (u,false)
def oddWire (u : Occ F) : Wire F Pad := .inl (u,true)

omit [DecidableEq V] in
theorem column_side_row (u : Occ F) : (N).row (evenWire F Pad u)=.inr (.inl u) := rfl

omit [DecidableEq V] in
theorem row_side_column (u : Occ F) : (N).col (oddWire F Pad u)=.inr (.inl u) := rfl

omit [DecidableEq V] in
theorem old_row_ports (e : F) (w : Wire F Pad) :
    (N).row w=.inl e ↔ ∃ b : Bool, w=oddWire F Pad (e,b) := by
  rcases w with ⟨u,b⟩|z
  · rcases u with ⟨u,d⟩
    cases b <;> simp [network,oddWire]
  · simp [network,oddWire]

omit [DecidableEq V] in
theorem old_column_ports (v : V) (w : Wire F Pad) :
    (N).col w=.inl v ↔ ∃ u : Occ F, endpoint F u=v ∧ w=evenWire F Pad u := by
  rcases w with ⟨u,b⟩|z
  · cases b
    · constructor
      · intro h
        exact ⟨u,Sum.inl.inj h,rfl⟩
      · rintro ⟨s,h,hh⟩
        have eq : u=s := congrArg Prod.fst (Sum.inl.inj hh)
        exact congrArg Sum.inl (by rw [eq]; exact h)
    · simp [network,evenWire]
  · simp [network,evenWire]

omit [DecidableEq V] in
theorem dummy_row_unique (z : Occ F ⊕ Pad) (w : Wire F Pad) :
    (N).row w=.inr z ↔ w=z.elim (evenWire F Pad) Sum.inr := by
  rcases z with u|z <;> rcases w with ⟨w,b⟩|p
  · cases b <;> simp [network,evenWire]
  · simp [network,evenWire]
  · cases b <;> simp [network]
  · simp [network]

omit [DecidableEq V] in
theorem dummy_col_unique (z : Occ F ⊕ Pad) (w : Wire F Pad) :
    (N).col w=.inr z ↔ w=z.elim (oddWire F Pad) Sum.inr := by
  rcases z with u|z <;> rcases w with ⟨w,b⟩|p
  · cases b <;> simp [network,oddWire]
  · simp [network,oddWire]
  · cases b <;> simp [network]
  · simp [network]

omit [DecidableEq V] in
/-- Negative-center comparison will join disjoint physical stars.
Every real wire has a degree-one endpoint in the original graph. -/
theorem every_wire_has_unary_side (w : Wire F Pad) :
    (∀ x, (N).row x=(N).row w → x=w) ∨ (∀ x,(N).col x=(N).col w → x=w) := by
  rcases w with ⟨u,b⟩|z
  · cases b
    · exact Or.inl fun x h=>(dummy_row_unique F Pad (.inl u) x).1 h
    · exact Or.inr fun x h=>(dummy_col_unique F Pad (.inl u) x).1 h
  · exact Or.inl fun x h=>(dummy_row_unique F Pad (.inr z) x).1 h

def incidence (v : V) :
    {u : Occ F // endpoint F u=v} ≃
      ((F.filter fun e=>e.1=v) ⊕ (F.filter fun e=>e.2=v)) where
  toFun u := match u with
    | ⟨(e,false),h⟩=>.inl ⟨e.val,Finset.mem_filter.mpr ⟨e.property,h⟩⟩
    | ⟨(e,true),h⟩=>.inr ⟨e.val,Finset.mem_filter.mpr ⟨e.property,h⟩⟩
  invFun s := match s with
    | .inl e=>⟨(⟨e.val,(Finset.mem_filter.mp e.property).1⟩,false),
         (Finset.mem_filter.mp e.property).2⟩
    | .inr e=>⟨(⟨e.val,(Finset.mem_filter.mp e.property).1⟩,true),
         (Finset.mem_filter.mp e.property).2⟩
  left_inv u := by rcases u with ⟨⟨e,b⟩,h⟩; cases b <;> rfl
  right_inv e := by rcases e with e|e <;> rfl

theorem incidence_card (v : V) :
    Nat.card {u : Occ F // endpoint F u=v}=GraphCutMoments.degree F v := by
  rw [Nat.card_congr (incidence F v),Nat.card_sum]
  unfold GraphCutMoments.degree
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_coe]

def colFibre (v : V) : {w : Wire F Pad // (N).col w=.inl v} ≃
    {u : Occ F // endpoint F u=v} where
  toFun w := by
    rcases w with ⟨⟨u,b⟩|z,h⟩
    · cases b
      · exact ⟨u,Sum.inl.inj h⟩
      · cases h
    · cases h
  invFun u := ⟨evenWire F Pad u.val,congrArg Sum.inl u.property⟩
  left_inv w := by
    rcases w with ⟨⟨u,b⟩|z,h⟩
    · cases b
      · rfl
      · cases h
    · cases h
  right_inv u := rfl

theorem real_column_degree (v : V) :
    Nat.card {w : Wire F Pad // (N).col w=.inl v}=GraphCutMoments.degree F v :=
  (Nat.card_congr (colFibre F Pad v)).trans (incidence_card F v)

def rowFibre (e : F) : {w : Wire F Pad // (N).row w=.inl e} ≃ Bool where
  toFun w := by
    rcases w with ⟨⟨u,b⟩|z,h⟩
    · cases b
      · cases h
      · exact u.2
    · cases h
  invFun b := ⟨oddWire F Pad (e,b),rfl⟩
  left_inv w := by
    rcases w with ⟨⟨⟨s,q⟩,b⟩|z,h⟩
    · cases b
      · cases h
      · have eq : s=e := Sum.inl.inj h
        subst s
        rfl
    · cases h
  right_inv _ := rfl

omit [DecidableEq V] in
theorem real_row_degree (e : F) :
    Nat.card {w : Wire F Pad // (N).row w=.inl e}=2 := by
  rw [Nat.card_congr (rowFibre F Pad e),Nat.card_eq_fintype_card,Fintype.card_bool]

omit [DecidableEq V] in
theorem physical_wire_count [Finite Pad] :
    Nat.card (Wire F Pad) = 2*(2*F.card)+Nat.card Pad := by
  simp only [Wire,Occ,Nat.card_sum,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe,
    Fintype.card_bool]
  ring

#print axioms every_wire_has_unary_side
#print axioms old_row_ports
#print axioms old_column_ports
#print axioms dummy_row_unique
#print axioms dummy_col_unique
#print axioms incidence_card
#print axioms real_row_degree
#print axioms real_column_degree
#print axioms physical_wire_count
end A1R43Literal
