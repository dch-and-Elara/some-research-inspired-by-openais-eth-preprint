
import RootEntry
import S11Kernel

noncomputable section
namespace RootSeparation.Solver
open RootSeparation.Entry
open GraphCutMoments
open scoped BigOperators

/-- Vertices and physical wires of a bipartite tensor network.
    Tables are indexed only by their genuine incident ports. -/
structure Network (R : Type*) where
  Wire : Type
  Row : Type
  Col : Type
  finiteWire : Fintype Wire
  finiteRow : Fintype Row
  finiteCol : Fintype Col
  row : Wire → Row
  col : Wire → Col
  rowEntry : (x : Row) → ({w // row w = x} → Bool) → R
  colEntry : (y : Col) → ({w // col w = y} → Bool) → R

attribute [instance] Network.finiteWire Network.finiteRow Network.finiteCol

namespace Network
variable {R : Type*} [CommSemiring R]

def rowProduct (N : Network R) (b : N.Wire → Bool) : R :=
  ∏ x, N.rowEntry x (fun w => b w.val)

def colProduct (N : Network R) (b : N.Wire → Bool) : R :=
  ∏ y, N.colEntry y (fun w => b w.val)

/-- Frozen leaf semantics. This sum is also the mathematical meaning
    of a network at an active call. -/
def contract (N : Network R) : R := by
  classical
  letI : Fintype N.Wire := N.finiteWire
  exact ∑ b : N.Wire → Bool, N.rowProduct b * N.colProduct b

variable {S : Type*} [CommSemiring S]
def map (φ : R →+* S) (N : Network R) : Network S :=
  { N with
    rowEntry := fun x u => φ (N.rowEntry x u)
    colEntry := fun y u => φ (N.colEntry y u) }

theorem map_rowProduct (φ : R →+* S) (N : Network R) (b : N.Wire → Bool) :
    (N.map φ).rowProduct b = φ (N.rowProduct b) := by
  simp [rowProduct, Network.map, map_prod]

theorem map_colProduct (φ : R →+* S) (N : Network R) (b : N.Wire → Bool) :
    (N.map φ).colProduct b = φ (N.colProduct b) := by
  simp [colProduct, Network.map, map_prod]

theorem map_contract (φ : R →+* S) (N : Network R) :
    (N.map φ).contract = φ N.contract := by
  classical
  simp only [contract, map_rowProduct, map_colProduct, map_sum, map_mul]
  rfl

end Network

section Entry

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (σ : V → Bool)

private abbrev PortAt (x : OldVertex E) := {w : Wire E // row E reg w = x}

/-- Equality halves, unary pins, and positive ORs use the local incidence
    table of Entry. Internal equality-tree wires are real ports. -/
def oldAccept (x : OldVertex E) : (PortAt E reg x → Bool) → Prop :=
  match x with
  | .inl (v,b) => fun a => ∀ w, a w = a ⟨(.inr v,b),rfl⟩
  | .inr (.inl v) => fun a => a ⟨S8.Uncloned.pin E v,rfl⟩ = σ v
  | .inr (.inr e) => fun a =>
      a ⟨(.inl (.inr (e,false)),true),rfl⟩ = true ∨
      a ⟨(.inl (.inr (e,true)),true),rfl⟩ = true

def subdivisionAccept (e : OriginalEdge E) :
    ({w : Wire E // column E w = e} → Bool) → Prop :=
  fun a => a ⟨(e,false),rfl⟩ = a ⟨(e,true),rfl⟩

omit [Fintype V] in
theorem accepts_factorization (b : Wire E → Bool) :
    S8.Uncloned.accepts E reg σ b ↔
      (∀ x, oldAccept E reg σ x (fun w => b w.val)) ∧
      (∀ y, subdivisionAccept E y (fun w => b w.val)) := by
  constructor
  · rintro ⟨hs,he,hp,hc⟩
    refine ⟨?_,hs⟩
    rintro (⟨v,d⟩ | v | e)
    · rintro ⟨⟨(q | v'),side⟩,hw⟩
      · cases side
        · simp only [Entry.row, S8.Uncloned.old] at hw
          have hab := Sum.inl.inj hw
          change b (.inl q,false) = b (.inr v,d)
          exact (he q).trans (congrArg (fun h : V × Bool => b (.inr h.1,h.2)) hab)
        · rcases q with (w | ⟨e,s⟩) <;> cases hw
      · change (.inl (v',side) : OldVertex E) = .inl (v,d) at hw
        have hab := Sum.inl.inj hw
        change b (.inr v',side) = b (.inr v,d)
        exact congrArg (fun h : V × Bool => b (.inr h.1,h.2)) hab
    · exact hp v
    · exact hc e
  · rintro ⟨ho,hs⟩
    refine ⟨hs,?_,?_,?_⟩
    · intro q
      exact (ho (.inl ((S8.Uncloned.slot E reg q).1,(S8.Uncloned.slot E reg q).2.1)))
        ⟨(.inl q,false),by simp only [Entry.row, S8.Uncloned.old]⟩
    · intro v
      exact ho (.inr (.inl v))
    · intro e
      exact ho (.inr (.inr e))

def entryNetwork (R : Type*) [CommSemiring R] : Network R where
  Wire := Wire E
  Row := OldVertex E
  Col := OriginalEdge E
  finiteWire := inferInstance
  finiteRow := inferInstance
  finiteCol := inferInstance
  row := row E reg
  col := column E
  rowEntry := fun x a => by classical exact if oldAccept E reg σ x a then 1 else 0
  colEntry := fun x a => by classical exact if subdivisionAccept E x a then 1 else 0

open Classical in
private theorem indicator_prod {A R : Type*} [Fintype A] [CommSemiring R] (P : A → Prop) :
    (∏ x, (if P x then (1:R) else 0)) = if ∀ x, P x then 1 else 0 := by
  classical
  by_cases h : ∀ x, P x
  · simp [h]
  · obtain ⟨x,hx⟩ := not_forall.mp h
    rw [if_neg h, Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx)]

open Classical in
theorem entryNetwork_factor (R : Type*) [CommSemiring R] (b : Wire E → Bool) :
    (entryNetwork E reg σ R).rowProduct b * (entryNetwork E reg σ R).colProduct b =
      if S8.Uncloned.accepts E reg σ b then 1 else 0 := by
  classical
  unfold Network.rowProduct Network.colProduct entryNetwork
  rw [indicator_prod, indicator_prod, accepts_factorization E reg σ b]
  by_cases h₁ : ∀ x, oldAccept E reg σ x (fun w => b w.val)
  · by_cases h₂ : ∀ y, subdivisionAccept E y (fun w => b w.val)
    · rw [if_pos h₁, if_pos h₂, if_pos ⟨h₁,h₂⟩, one_mul]
    · rw [if_pos h₁, if_neg h₂, if_neg (fun h => h₂ h.2), mul_zero]
  · have hn : ¬ ((∀ x, oldAccept E reg σ x (fun w => b w.val)) ∧
        (∀ y, subdivisionAccept E y (fun w => b w.val))) := fun h => h₁ h.1
    rw [if_neg h₁, if_neg hn, zero_mul]

theorem entryNetwork_contract (R : Type*) [CommSemiring R] :
    (entryNetwork E reg σ R).contract = (PinnedCNF.modelCount (PinnedCNF.formula E σ) : R) := by
  classical
  rw [← Entry.network_count E reg σ]
  unfold Network.contract S8.Uncloned.networkCount
  simp_rw [entryNetwork_factor E reg σ R]
  rw [← Finset.sum_filter]
  simp

end Entry

#print axioms Network.map_contract
#print axioms accepts_factorization
#print axioms entryNetwork_contract

end RootSeparation.Solver

