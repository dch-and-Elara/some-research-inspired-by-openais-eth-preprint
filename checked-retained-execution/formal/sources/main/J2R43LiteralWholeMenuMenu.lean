import J2R43LiteralWholeMenuFactors
import J2R43LiteralWholeMenuAddress
import J2R43LiteralWholeMenuGuard
import J9R15FrozenErasurePrecision
import P5D1LiteralResponse

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 16
set_option maxRecDepth 2100
set_option linter.unusedSectionVars false

/-! Erase every legal original old-row completed slot at a common lower
precision. Modes and physical children remain those at their high precision. -/
namespace J2R43LiteralWholeMenu
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral J6R11Integral
open J6R9PacketScopes J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral
open Paper5.D1Literal Paper5.HybridClosure J1PPrinted
open J9R15FrozenErasurePhysical J9R15FrozenErasurePrecision

noncomputable section
variable {W : Type} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {reg : ∀ v,GraphCutMoments.degree F v=3}
variable [Nonempty (MainClonedCNF.Port F)]
variable {a : ℕ} {f : ℤ[X]}
local notation "E" => (DWire F)
local notation "C" => (MainClonedCNF.Port F)
local notation "N" => (dNetwork F reg)

theorem true_whole_low_zero (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p q : ℕ) (fit : q≤p) (z : Box f 1 p) (hf : f.Monic) (hd : 0<f.natDegree)
    (σ : W→Bool) (β : Mode i p P.mask →₀ ℕ)
    (deep : q≤(actualKept P t).card) :
    lowerBox p q fit f 1
      (actualProjection P i ht hv p z (oldRowFile F reg f (4*Fintype.card W+1) σ) hf β)=0 := by
  exact J9R15FrozenErasureGeneric.projected_zero P i ht hv p z
    (oldRowFile F reg f (4*Fintype.card W+1) σ) hf Finset.univ (vertexOwner P.seat)
    (actualTail P t σ) (source_frozen_split P t f hf hd _ p (by omega) σ)
    (lowerBox p q fit f 1) (actual_old_ports P) q (box_two_nil q f 1) deep β


theorem literal_public_slot_erases (P : RootPacking F reg f)
    (d : Ready (printedParams (f:=f) (ell:=1) (oldRowSize F)) (sourceDelta (oldRowSize F)) (oldRowRoot F reg f (fun _=>false)))
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (deep : sourceQ F f≤(actualKept P x.1.val).card) :
    observedSlot P d hf σ x=0 := by
  rw [literal_public_slot_is_projected_slot]
  exact true_whole_low_zero P (PublicIndex F reg f d x.1) (centerNonzero x.1) rfl
    (noncePrec F reg f x.1) (sourceQ F f) (sourceQ_fits x.1)
    (sampleNode (printedParams (f:=f) (ell:=1) (oldRowSize F)) f 1 (oldRowRoot F reg f (fun _=>false)) d.fit x.1 x.2.1) hf hd σ x.2.2.val deep
/-- Fix one such packing before any sign, center, probe, or mode. The
same labels and common load are preserved exactly. -/
theorem whole_printed_menu (P : RootPacking F reg f)
    (d : Ready (printedParams (f:=f) (ell:=1) (oldRowSize F)) (sourceDelta (oldRowSize F)) (oldRowRoot F reg f (fun _=>false)))
    (hf : f.Monic) (hd : 0<f.natDegree)
    (hU : 1≤J9PrintedSchedule.rootU (Nat.clog 2 (oldRowSize F))) (size : 320^2≤oldRowSize F) :
    ∃ Q : RootPacking F reg f,
      Q.rowLabel=P.rowLabel ∧ Q.colLabel=P.colLabel ∧ Q.copies=P.copies ∧
      Fintype.card E≤8*2^((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)*sourceQ F f ∧
      ∀ σ : W→Bool, ∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0 := by
  have ha : 0<(printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0 := by
    have h := stepA_ge_root (Nat.clog 2 (oldRowSize F)) 0
    change 0<stepA (Nat.clog 2 (oldRowSize F)) 0
    omega
  obtain ⟨Q,hr,hc,hb,hAll⟩ := all_shift_guarded_packing ha P
  have room := literal_printed_guard (reg:=reg) (f:=f) hU size
  have hL : 0<(2^((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0):ℕ) := by positivity
  have hD : 1≤Fintype.card (Cell (Fin ((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)) (Fin 64)) := Fintype.card_pos
  have hs : 4*(2^((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0):ℕ)≤Fintype.card E := by nlinarith only [room,hD,hL]
  refine ⟨Q,hr,hc,hb,guardedQ_scale _ _ hL hs,?_⟩
  intro σ x
  exact literal_public_slot_erases Q d hf hd σ x
    (kept_depth_from_bound Q x.1.val room (hAll x.1.val (centerNonzero x.1)))

#print axioms true_whole_low_zero
#print axioms literal_public_slot_erases
#print axioms whole_printed_menu
end
end J2R43LiteralWholeMenu