import P6JointConstruct
import P6JointAtlasDegree

namespace Paper6JointSeating
open scoped Classical BigOperators
open P11FullPacking P9BalancedChart
open J7SourceLabels J7SeatSource J7PrintedParamsGraph J9R20SameFile

noncomputable section
set_option linter.unusedSectionVars false

variable {Pair H A : Type} [Fintype Pair] [Fintype H] [LinearOrder A] [Fintype A]
variable (ends : H×Bool ≃ Pin Pair×Fin 3)
variable {a b : ℕ} (label : Wires Pair H → Cell (Fin a) A)

local notation "W" => Wires Pair H
local notation "E" => Clones Pair
local notation "M" => Fintype.card W
local notation "B" => ((2*(Fintype.card E : ℝ)+9*(M:ℝ))/(2^a:ℕ))

theorem literalJointPlacement (ha : 0<a)
    (matching : Finset W) (hm : matching ⊆ publicNonpins ends)
    (hr : Set.InjOn (rowNode Prod.fst) {w | w ∈ matching})
    (cap : ∀ c, Nat.card (RealFiber label c) ≤ b*2^a)
    (pool : ∀ c, 2*b ≤ (ofCell label (publicNonpins ends) c).card)
    (margin : ∀ c, 2*(b:ℝ)+(ofCell label matching c).card/(2^a:ℕ)+Real.sqrt B
      ≤ (ofCell label matching c).card) :
    ∃ (seat : W ↪ Physical a b A) (keep : Bool → Finset E),
      Disjoint (keep false) (keep true) ∧
      (∀ s, (Fintype.card E : ℝ)/(2^a:ℕ) ≤ (keep s).card +
        Real.sqrt B + Real.sqrt ((Fintype.card (Cell (Fin a) A) : ℝ)*B)) ∧
      (∀ w, physicalCell (balancedMask a b A) (seat w) = label w) ∧
      (∀ w s e, colNode (column ends cycle) w = .inr (cloneOwner e) →
        e ∈ keep s → (seat w).2 = endpointIndex a s) ∧
      (∀ z s, z.2 = endpointIndex a s → ∃ w, seat w = z) ∧
      (∀ w s, (seat w).2 = endpointIndex a s → nonpin (column ends cycle) w) ∧
      Set.InjOn (rowNode Prod.fst) {w | (seat w).2 = endpointIndex a false} := by
  obtain ⟨seat,keep,hd,hq,hlabel,hmark,hfull,hpin,hrow⟩ :=
    joint_from_matching ha label (rowNode Prod.fst) (associatedClone ends)
      cloneWires matching (publicNonpins ends) (cloneWires_nonpin ends) hm
      (fun _ hx _ hy => clone_wire_of_injOn (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2)
      hr (associatedClone_eq_of_row ends) (clone_port_cap ends) (match_clone_cap ends matching hr)
      cap pool B (by positivity) le_rfl margin
  refine ⟨seat,keep,hd,hq,hlabel,?_,hfull,?_,hrow⟩
  · intro w s e hw he
    obtain ⟨hp,hown⟩ := clone_port_owner_reverse ends w e hw
    exact hmark w s (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩) (hown.symm ▸ he)
  · intro w s hw
    exact (Finset.mem_filter.mp (hpin w s hw)).2

#print axioms literalJointPlacement
end
end Paper6JointSeating
