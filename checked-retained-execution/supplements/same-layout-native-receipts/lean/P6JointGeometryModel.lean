import P6JointGeometryTransport
import P6JointAtlas
import J9R20SameFilePublicWorld

namespace Paper6JointSeating
open scoped Classical BigOperators Polynomial
open Polynomial J7SourceLabels J7PrintedParams J7PrintedParamsGraph J7ToJ8Incidence J7ToJ8Layout
open J7SeatSource P11FullPacking J7SeatPacking J7SeatRounded J7ToJ8Canonical
open J6R10Repack J6R9PacketScopes J8Physical J6R14SpecializedBox J1PPrinted J9R20SameFile

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool ≃ Pin Pair×Fin 3)
local notation "N₀" => Fintype.card (Pin Pair)
local notation "R" => Subdivision Pair (OrdinaryRow Pair H)
local notation "E" => J8Physical.Wire R
local notation "T" => (column ends cycle)
local notation "G" => Fin 64
local notation "D" => PrintedOld Pair H
local notation "U" => Clones Pair

structure JointSourceGeometry (a b : ℕ) where
  layout : Layout (Page a b G) R (Pin Pair) D G (Ports T) (2^a)
  wordsR : R→Fin a→G
  wordsC : Pin Pair⊕D→Fin a→G
  declared : ∀ w : E, physicalCell (balancedMask (K:=G) a b) (layout.seat w) =
    declaredCell (orientedNetwork layout) wordsR wordsC w
  budget : Nat.card (Cell (Fin a) G)*(b*2^a) ≤ 3*Nat.card E
  capacity : 2^a*Fintype.card (Page a b G)≤3*Fintype.card E
  rowHead : ∀ i : Fin a, i.val=0 → ∀ w : E,
    rowGroup (balancedMask (K:=G) a b) i (layout.seat w)=layout.rowLabel w.1
  colHead : ∀ i : Fin a, i.val=0 → ∀ w : E,
    colGroup (balancedMask (K:=G) a b) i (layout.seat w)=actualColLabel layout w
  endpoint : J8Physical.Relaxed.RowEndpointSeating layout
  off : ∀ s : Pin Pair, layout.rowLabel (pinWire layout s).1 ≠ layout.pinLabel s
  keep : Bool → Finset U
  disjoint : Disjoint (keep false) (keep true)
  guard_seated : ∀ s x, x ∈ keep s → ∀ w : E, colOwner layout w = .inr (cloneOwner x) →
    (layout.seat w).2.val = GuardedPacking.endpoint (2^a) s
  guard_size : ∀ s,
    let B := (2*(Fintype.card U:ℝ)+9*(Fintype.card E:ℝ))/(2^a:ℕ)
    (Fintype.card U:ℝ)/(2^a:ℕ) ≤ (keep s).card + Real.sqrt B +
      Real.sqrt ((Fintype.card (Cell (Fin a) G):ℝ)*B)

end
end Paper6JointSeating
