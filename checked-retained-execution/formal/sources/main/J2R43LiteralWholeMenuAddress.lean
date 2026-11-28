import J2R43LiteralWholeMenuGeometry
import J2R43LiteralWholeMenuScale
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

theorem kept_depth_from_bound (P : PhysicalPacking N a (Fin 64)) (t : ℤ)
    (room : 320*Fintype.card (Cell (Fin a) (Fin 64))*2^a≤Fintype.card E)
    (bound : (Fintype.card C:ℝ)/((2^a:ℕ):ℝ)≤ (actualKept P t).card+errBudget F a) :
    guardedQ (Fintype.card E) (2^a)≤(actualKept P t).card := by
  have hM : 2*Fintype.card C=Fintype.card E := by
    change 2*Fintype.card C=Fintype.card (C×Bool)
    rw [Fintype.card_prod,Fintype.card_bool,mul_comm]
  have hMr : 2*(Fintype.card C:ℝ)=(Fintype.card E:ℝ) := by exact_mod_cast hM
  have hD : 1≤Fintype.card (Cell (Fin a) (Fin 64)) := Fintype.card_pos
  have hL : 0<(2^a:ℕ) := by positivity
  apply guardedQ_from_two_errors _ _ _ _ hD hL room
  rw [←hMr,mul_div_mul_left _ _ (by norm_num : (2:ℝ)≠0)]
  unfold errBudget at bound
  linarith only [bound]


abbrev sourceQ (F : Finset (W×W)) (f : ℤ[X]) :=
  guardedQ (Fintype.card (DWire F))
    (2^(printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)

abbrev noncePrec (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
    (f : ℤ[X]) (t : PublicCenter F reg f) :=
  registerPrecision (printedParams (f:=f) (ell:=1) (oldRowSize F))
    (oldRowRoot F reg f (fun _=>false)) t

theorem sourceQ_fits (t : PublicCenter F reg f) :
    sourceQ F f≤noncePrec F reg f t := by
  unfold sourceQ guardedQ
  apply (Nat.div_le_self _ _).trans
  change Fintype.card E ≤ J9PrintedSchedule.precision (4*Fintype.card W+1)
    (J6ActiveSchedule.height (Fintype.card E) ((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelWidth 0))
    (2^((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)/2^padicValInt 2 t.val) (Fintype.card E) ((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)
  unfold J9PrintedSchedule.precision
  have h : Fintype.card E ≤ 8 * Fintype.card E * ((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0+1) := by nlinarith
  omega

/-- The observer of the very same root address, not of a changed child,
projecting the product only after looking up the true high menu. -/
def observedSlot (P : RootPacking F reg f) (d : Ready (printedParams (f:=f) (ell:=1) (oldRowSize F)) (sourceDelta (oldRowSize F)) (oldRowRoot F reg f (fun _=>false)))
    (hf : f.Monic) (σ : W→Bool) (x : PublicSlot F reg f P d) : Box f 1 (sourceQ F f) :=
  lowerBox (noncePrec F reg f x.1) (sourceQ F f) (sourceQ_fits x.1) f 1
    (∏ g : Fin 64, publicReply F reg f P d hf σ ⟨x.1,x.2.1,x.2.2,g⟩)


/-- The child reply product is from the identical public address, including
exact binary probe and high-precision mode. -/
theorem literal_public_slot_is_projected_slot (P : RootPacking F reg f)
    (d : Ready (printedParams (f:=f) (ell:=1) (oldRowSize F)) (sourceDelta (oldRowSize F)) (oldRowRoot F reg f (fun _=>false)))
    (hf : f.Monic) (σ : W→Bool) (x : PublicSlot F reg f P d) :
    observedSlot P d hf σ x =
      lowerBox (noncePrec F reg f x.1) (sourceQ F f) (sourceQ_fits x.1) f 1
        (actualProjection P (PublicIndex F reg f d x.1) (centerNonzero x.1) rfl
          (noncePrec F reg f x.1) (sampleNode (printedParams (f:=f) (ell:=1) (oldRowSize F)) f 1 (oldRowRoot F reg f (fun _=>false)) d.fit x.1 x.2.1)
          (oldRowFile F reg f (4*Fintype.card W+1) σ) hf x.2.2.val) := by
  let i := PublicIndex F reg f d x.1
  let p := noncePrec F reg f x.1
  let z := sampleNode (printedParams (f:=f) (ell:=1) (oldRowSize F)) f 1 (oldRowRoot F reg f (fun _=>false)) d.fit x.1 x.2.1
  let file := oldRowFile F reg f (4*Fintype.card W+1) σ
  have h : (∏ g : Fin 64, publicReply F reg f P d hf σ ⟨x.1,x.2.1,x.2.2,g⟩)=
      actualProjection P i (centerNonzero x.1) rfl p z file hf x.2.2.val := by
    unfold actualProjection
    apply Finset.prod_congr rfl
    intro g _
    change reduce p f 1 ((publicChildHost F reg f P d σ ⟨x.1,x.2.1,x.2.2,g⟩).contract hf)=_
    exact congrArg (reduce p f 1)
      (actualPacketHost_truth P i (centerNonzero x.1) rfl p z file hf x.2.2.val g)
  exact congrArg (lowerBox p (sourceQ F f) (sourceQ_fits x.1) f 1) h
include reg in
theorem literal_printed_guard (hU : 1≤J9PrintedSchedule.rootU (Nat.clog 2 (oldRowSize F)))
    (size : 320^2≤oldRowSize F) :
    320*Fintype.card (Cell (Fin ((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)) (Fin 64))*2^((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)≤Fintype.card E := by
  have hE := d_physical_wire_count F reg
  have hs := oldRow_size_exact F reg
  have hMass : oldRowSize F≤Fintype.card E := by omega
  have hD : Fintype.card (Cell (Fin ((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)) (Fin 64)) =
      J9PrintedSchedule.arrayCard ((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0) := by
    rw [← Nat.card_eq_fintype_card,total_cells,Fintype.card_fin]
    rfl
  rw [hD]
  exact printed_guard_small _ 0 _ hU size hMass

#print axioms kept_depth_from_bound
#print axioms sourceQ_fits
#print axioms literal_public_slot_is_projected_slot
#print axioms literal_printed_guard
end
end J2R43LiteralWholeMenu