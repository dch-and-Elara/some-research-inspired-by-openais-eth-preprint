import SolverNetwork
import S11ChildPorts
import S8DChild
import RootProgram

noncomputable section
namespace RootSeparation.Solver
open S11
open scoped BigOperators

section Children

variable {R S : Type*} [CommSemiring R] [CommSemiring S]
variable (N : Network R) {P : Type} [Fintype P] {a L : ℕ}
variable (left : N.Row → Fin a → Fin 64) (right : N.Col → Fin a → Fin 64)
variable (i : Fin a) (g : Fin 64)

abbrev RetainedOld := {v : N.Row ⊕ N.Col // S8.DChild.symbol left right i v = g}
abbrev ChildEdge := S8.DChild.Edge N.row N.col left right i g

def oldEndpoint : ChildEdge N left right i g → RetainedOld N left right i g :=
  S8.DChild.childOld N.row N.col left right i g

def packetEndpoint (put : N.Wire ↪ P × Fin L) (w : ChildEdge N left right i g) : P :=
  S8.DChild.childPacket put w

def oldTable (φ : R →+* S) (v : RetainedOld N left right i g)
    (b : {w // oldEndpoint N left right i g w = v} → Bool) : S := by
  rcases v with ⟨v|v,hv⟩
  · apply φ (N.rowEntry v ?_)
    intro w
    exact b ⟨⟨(w.val,false), by simpa [S8.DChild.oldEndpoint,S8.DChild.symbol,w.property] using hv⟩,
      Subtype.ext (by simpa [oldEndpoint,S8.DChild.childOld,S8.DChild.oldEndpoint] using w.property)⟩
  · apply φ (N.colEntry v ?_)
    intro w
    exact b ⟨⟨(w.val,true), by simpa [S8.DChild.oldEndpoint,S8.DChild.symbol,w.property] using hv⟩,
      Subtype.ext (by simpa [oldEndpoint,S8.DChild.childOld,S8.DChild.oldEndpoint] using w.property)⟩

/-- Each old port gets its own edge. Row and column endpoints of one
parent wire can both occur in the same child without being merged. -/
def childNetwork (φ : R →+* S) (put : N.Wire ↪ P × Fin L)
    (table : (p : P) → ({w // packetEndpoint N left right i g put w = p} → Bool) → S) :
    Network S := by
  classical
  letI : Fintype N.Row := N.finiteRow
  letI : Fintype N.Col := N.finiteCol
  letI : Fintype N.Wire := N.finiteWire
  exact {
    Wire := ChildEdge N left right i g
    Row := RetainedOld N left right i g
    Col := P
    finiteWire := inferInstance
    finiteRow := inferInstance
    finiteCol := inferInstance
    row := oldEndpoint N left right i g
    col := packetEndpoint N left right i g put
    rowEntry := oldTable N left right i g φ
    colEntry := table }

theorem childNetwork_card (φ : R →+* S) (G : Packing N.Wire P a L)
    (h : G.cell = S8.DChild.rootCell N.row N.col left right)
    (table : (p : P) → ({w // packetEndpoint N left right i g G.position w = p} → Bool) → S) :
    Fintype.card (childNetwork N left right i g φ G.position table).Wire =
      Fintype.card (S11.ChildWire G i g) := by
  classical
  apply Fintype.card_congr
  let e₀ : ChildEdge N left right i g ≃
      {w : N.Wire // left (N.row w) i = g} ⊕ {w : N.Wire // right (N.col w) i = g} :=
    { toFun := fun w => match w with
        | ⟨(w,false),hw⟩ => .inl ⟨w,hw⟩
        | ⟨(w,true),hw⟩ => .inr ⟨w,hw⟩
      invFun := Sum.elim (fun w => ⟨(w.val,false),w.property⟩)
        (fun w => ⟨(w.val,true),w.property⟩)
      left_inv := by rintro ⟨⟨w,b⟩,hw⟩; cases b <;> rfl
      right_inv := by rintro (w | w) <;> rfl }
  exact e₀.trans (Equiv.sumCongr (Equiv.subtypeEquivRight (fun w => by rw [h]; rfl))
    (Equiv.subtypeEquivRight (fun w => by rw [h]; rfl)))

/-- Source 6M/64 implies strict descent on the actual child incidence
type, independently of any coefficient values. -/
theorem childNetwork_shrink (φ : R →+* S) (G : Packing N.Wire P a L)
    (h : G.cell = S8.DChild.rootCell N.row N.col left right)
    (Δ : ℚ) (cert : SourceDensity.CollisionCertificate G.cell Δ)
    (table : (p : P) → ({w // packetEndpoint N left right i g G.position w = p} → Bool) → S) :
    8 * Fintype.card (childNetwork N left right i g φ G.position table).Wire ≤ Fintype.card N.Wire := by
  rw [childNetwork_card N left right i g φ G h]
  exact child_wire_source_eighth G i g Δ cert

end Children

section Packet
variable {R : Type*} [CommSemiring R]
variable {Rows Modes : Type*} [Fintype Rows] [Fintype Modes]

/-- Extract the coefficient using one choice from each real affine
row. The Option.none term is the local term of that row. -/
def packetCoeff (row : Rows → Option Modes → R) (β : Modes → ℕ) : R := by
  classical
  exact ∑ c : Rows → Option Modes,
    if ∀ z, Fintype.card {r // c r = some z} = β z then ∏ r, row r (c r) else 0

/-- Its source-side powers are evaluated using the very same
assignment as the local target coefficient. Empty products use 1. -/
def packetValue {Reads : Type*} [Fintype Reads]
    (row : Rows → Option Modes → R) (β : Modes → ℕ)
    (read : Reads → R) (powers : Reads → ℕ) : R :=
  packetCoeff row β * ∏ z, read z ^ powers z

theorem packetCoeff_empty_rows [IsEmpty Rows] (row : Rows → Option Modes → R)
    (β : Modes → ℕ) : packetCoeff row β = if β = 0 then 1 else 0 := by
  classical
  let c : Rows → Option Modes := isEmptyElim
  unfold packetCoeff
  rw [Finset.sum_eq_single c]
  · have h : (∀ z, Fintype.card {r // c r = some z} = β z) ↔ β = 0 := by
      simp only [Fintype.card_of_isEmpty]
      constructor
      · intro hc
        funext z
        exact (hc z).symm
      · intro hz
        rw [hz]
        intro z
        rfl
    simp only [h,Fintype.prod_empty]
  · intro q _ h
    exact (h (funext isEmptyElim)).elim
  · intro h
    exact (h (@Finset.mem_univ _ (@Pi.instFintype Rows (fun _ => Option Modes)
      (Classical.decEq Rows) _ _) c)).elim

end Packet

#print axioms childNetwork_card
#print axioms childNetwork_shrink
#print axioms packetCoeff_empty_rows

end RootSeparation.Solver
