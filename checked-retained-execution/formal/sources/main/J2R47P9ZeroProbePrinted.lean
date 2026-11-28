import J2R47P9ZeroProbeJoint
import J2R47P9ZeroProbeDepth
import J2R43LiteralWholeMenuMenu

/-! Both conclusions concern ONE source layout: the fixed smaller
completion precision at every original probe, and the unchanged full
native receiver at any originally delivered zero probe. -/
namespace J2R47P9ZeroProbe
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking P9BalancedChart J6R10Repack J6R12Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
open J2R43LiteralWholeMenu J1PPrinted
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 2600
set_option Elab.async false
set_option linter.unusedSectionVars false
noncomputable section

variable {W : Type} [finiteW : Fintype W] [decW : DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "E" => DWire F
local notation "C" => MainClonedCNF.Port F
local notation "N" => (dNetwork F reg)
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "A" => (J6ActiveRun.Shape.levelBits (S) 0)
local notation "D" => Fintype.card (Cell (Fin A) (Fin 64))
local notation "L" => (2^A : ℕ)
local notation "M" => Fintype.card E

theorem enough_copies_for_reserved_ports (P : RootPacking F reg f)
    (room : 1280*D*L≤M) :
    4≤P.copies := by
  classical
  have actual : M≤D*(P.copies*L) := by
    calc
      M = Nat.card (DWire F) := Nat.card_eq_fintype_card.symm
      _ ≤ Nat.card (Physical A P.copies (Fin 64)) := Nat.card_le_card_of_injective P.seat P.seat.injective
      _ = _ := by
        rw [Nat.card_congr (fullSlotChart P.mask),Nat.card_prod,Nat.card_fin,
          Nat.card_eq_fintype_card (α:=Cell (Fin A) (Fin 64))]
  have hD : 0<D := Fintype.card_pos
  have hL : 0<L := by positivity
  by_contra! bad
  have hcopy : P.copies<1280 := by omega
  have h : D*(P.copies*L)<1280*D*L := by
    calc
      _ < D*(1280*L) := Nat.mul_lt_mul_of_pos_left
        (Nat.mul_lt_mul_of_pos_right hcopy hL) hD
      _ = _ := by ring
  omega

variable [neC : Nonempty (MainClonedCNF.Port F)]
theorem printed_kept_depth_with_reservation (Q : RootPacking F reg f) (t : ℤ)
    (room : 1280*D*L≤M)
    (bound : (Fintype.card C:ℝ)/(L:ℝ)≤(@actualKept W finiteW decW F reg A neC Q t).card+errBudget F A+6) :
    sourceQ F f≤(@actualKept W finiteW decW F reg A neC Q t).card := by
  have hM : 2*Fintype.card C=M := by
    change 2*Fintype.card C=Fintype.card (C×Bool)
    rw [Fintype.card_prod,Fintype.card_bool,mul_comm]
  have hMr : 2*(Fintype.card C:ℝ)=(M:ℝ) := by exact_mod_cast hM
  apply reserved_guardedQ M D L _ Fintype.card_pos (by positivity) room
  rw [←hMr,mul_div_mul_left _ _ (by norm_num : (2:ℝ)≠0)]
  simpa only [errBudget,add_assoc] using bound

include reg in
theorem actual_printed_reserved_room
    (hU : 1≤J9PrintedSchedule.rootU (Nat.clog 2 (oldRowSize F)))
    (size : 1280^2≤oldRowSize F) :
    1280*D*L≤M := by
  have hE := d_physical_wire_count F reg
  have hs := oldRow_size_exact F reg
  have hMass : oldRowSize F≤M := by omega
  have hD : D=J9PrintedSchedule.arrayCard A := by
    rw [← Nat.card_eq_fintype_card,total_cells,Fintype.card_fin]
    rfl
  rw [hD]
  exact printed_reserved_room _ 0 _ hU size hMass

/-- The source guard, original fixed common low precision, and original
full-native zero probes are jointly certified. No more precise nonzero
probe is returned, and a roster without zero receives no new address. -/
theorem same_printed_J2_layout_full_zero_probes
    (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))
    (positive negative : F) (distinct : positive≠negative)
    (hf : f.Monic) (hd : 0<f.natDegree)
    (hU : 1≤J9PrintedSchedule.rootU (Nat.clog 2 (oldRowSize F)))
    (size : 1280^2≤oldRowSize F) :
    ∃ Q : RootPacking F reg f,
      Q.rowLabel=P.rowLabel ∧ Q.colLabel=P.colLabel ∧ Q.copies=P.copies ∧
      Reserved F reg Q positive negative ∧
      (∀ t : PublicCenter F reg f, sourceQ F f≤(@actualKept W finiteW decW F reg A neC Q t.val).card) ∧
      (∀ (σ : W→Bool) (x : PublicSlot F reg f Q d),observedSlot Q d hf σ x=0) ∧
      ∀ (σ : W→Bool) (x : PublicSlot F reg f Q d),
        siteProbe F reg d x.1 x.2.1=0 → wholePublic F reg Q d hf σ x=0 := by
  have ha : 0<A := by
    have h := stepA_ge_root (Nat.clog 2 (oldRowSize F)) 0
    change 0<stepA (Nat.clog 2 (oldRowSize F)) 0
    omega
  have room : 1280*D*L≤M := actual_printed_reserved_room F (f:=f) reg hU size
  have hb := enough_copies_for_reserved_ports F reg P room
  obtain ⟨Q,row,col,copies,reserve,kept⟩ :=
    @source_p9_guard_and_reserved_or W finiteW decW F reg A neC P ha hb positive negative distinct
  have deep (t : PublicCenter F reg f) : sourceQ F f≤(@actualKept W finiteW decW F reg A neC Q t.val).card :=
    printed_kept_depth_with_reservation F reg (f:=f) Q t.val room (kept t.val (centerNonzero t))
  exact ⟨Q,row,col,copies,reserve,deep,
    (fun σ x=>@literal_public_slot_erases W finiteW decW F reg neC f Q d hf hd σ x (deep x.1)),
    reserved_endpoints_public_full_zero F reg Q d positive negative reserve hf hd⟩

#print axioms enough_copies_for_reserved_ports
#print axioms printed_kept_depth_with_reservation
#print axioms actual_printed_reserved_room
#print axioms same_printed_J2_layout_full_zero_probes
end
end J2R47P9ZeroProbe

