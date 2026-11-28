
import J7R13Literal
import J7R13Schedule
import J6R14SpecializedBoxPreservedMode
import J9R20SameFileCatalog

/-! Feed the actual J7 existence witness to the oriented source compiler.
The only casts here identify J7's root word length with the printed
recursive word length; no slot, word, or equality entry is changed. -/
namespace J9R20SameFile
open scoped Classical BigOperators Polynomial
open Polynomial J7SourceLabels J7PrintedParams J7PrintedParamsGraph J7ToJ8Incidence J7ToJ8Layout
open J7SeatSource P11FullPacking J7SeatPacking J7SeatRounded J7ToJ8Canonical
open J6R10Repack J6R9PacketScopes J8Physical J6R14SpecializedBox J1PPrinted
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool≃Pin Pair×Fin 3)
local notation "N₀" => Fintype.card (Pin Pair)
local notation "R" => Subdivision Pair (OrdinaryRow Pair H)
local notation "E" => J8Physical.Wire R
local notation "T" => (column ends cycle)
local notation "G" => Fin 64
local notation "D" => PrintedOld Pair H

structure SourceGeometry (a b : ℕ) where
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
  endpoint : EndpointSeating layout
  off : ∀ s : Pin Pair, layout.rowLabel (pinWire layout s).1 ≠ layout.pinLabel s

private theorem target_witness_implies_off
    {Packet Row S V K : Type} [Fintype Row] [LinearOrder K] {P : V→Type} {L : ℕ}
    (d : Layout Packet Row S V K P L) (s : S)
    (h : (targets d (pinWire d s)).Nonempty) :
    d.rowLabel (pinWire d s).1 ≠ d.pinLabel s := by
  obtain ⟨w,hw⟩ := h
  have hh := (Finset.mem_filter.mp hw).2
  have hr : d.rowLabel w.1=d.rowLabel (pinWire d s).1 := by
    rw [d.rowOrientation w,d.rowOrientation (pinWire d s),hh.1,hh.2.1]
  rw [hr,pinWire_colLabel] at hh
  exact hh.2.2

theorem original_source_geometry_at_printed_root
    (large : 2^(9*131072-1) < sourceSize N₀) :
    ∃ b, Nonempty (SourceGeometry ends (stepA (Nat.clog 2 (sourceSize N₀)) 0) b) := by
  let t := rootT (sourceSize N₀)
  have hU : 0<rootU (sourceSize N₀) := lt_of_lt_of_le (by decide : (0:ℕ)<9) (u_large _ large)
  rw [J7R13.root_bits_same _ hU]
  obtain ⟨_,z,cap,_,_,j,preserve,_,⟨ed⟩,_,_,pinTargets⟩ :=
    J7R13.literal_four_clone_scored_root (A:=G) (by simp) ends large
  let b := ceilCopies (2^(t+1)) (realMaximum (wordLabel Prod.fst T z))
  let d := physicalLayout Prod.fst T ordinary_row_exact_two z j preserve
  have hsize : Fintype.card E = 24*N₀ :=
    (Fintype.card_congr (d.column.trans (colWire T))).trans (actual_incidence ends).1
  have cap' : Nat.card (Page (t+1) b G)*2^(t+1)≤3*Nat.card E := by
    rw [Nat.card_eq_fintype_card (α:=E),hsize]
    exact cap
  have budget : Nat.card (Page (t+1) b G)*2^(t+1)≤3*Nat.card (J7SourceLabels.Wire Pair (OrdinaryWire Pair H)) := by
    rw [← Nat.card_congr (rowWire (Pair:=Pair) Prod.fst ordinary_row_exact_two)]
    exact cap'
  have hc : ∀ w : E, physicalCell (balancedMask (t+1) b) (d.seat w)=
      declaredCell (orientedNetwork d) (J7R13.rowFull z) (J7R13.colFull z) w := by
    intro w
    let e := rowWire (Pair:=Pair) Prod.fst ordinary_row_exact_two w
    have hf := (preserve e).trans (J7R13.actual_cell Prod.fst T z e)
    refine hf.trans ?_
    funext i
    change (J7R13.rowFull z (rowNode Prod.fst (rowWire Prod.fst ordinary_row_exact_two w)) i,
      J7R13.colFull z (colNode T (rowWire Prod.fst ordinary_row_exact_two w)) i) =
      (J7R13.rowFull z w.1 i, J7R13.colFull z (colOwner d w) i)
    exact Prod.ext
      (congrArg (fun v=>J7R13.rowFull z v i) (rowWire_owner Prod.fst ordinary_row_exact_two w))
      (congrArg (fun v=>J7R13.colFull z v i) (owner_layout Prod.fst T ordinary_row_exact_two z j preserve w).symm)
  refine ⟨b,⟨d,J7R13.rowFull z,J7R13.colFull z,hc,?_,?_,?_,?_,ed,?_⟩⟩
  · rwa [← total_slots (balancedMask (K:=G) (t+1) b)]
  · rw [Nat.mul_comm]
    simpa only [Nat.card_eq_fintype_card] using cap'
  · intro i hi w
    have eq : i=(0:Fin (t+1)) := Fin.ext hi
    rw [eq]
    exact preserved_row_chart Prod.fst T ordinary_row_exact_two z j preserve budget w
  · intro i hi w
    have eq : i=(0:Fin (t+1)) := Fin.ext hi
    rw [eq]
    exact preserved_col_chart Prod.fst T ordinary_row_exact_two z j preserve budget w
  · intro pin
    exact target_witness_implies_off d pin (pinTargets pin)

#print axioms original_source_geometry_at_printed_root
end
end J9R20SameFile
