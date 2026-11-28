
import J9R20SameFileHighAnchors
import J7R43LiteralPublicZero
import J7R43LiteralPostprocessPhysical
import J7R43LiteralDecoded
import J7R43LiteralRequests
import J7R43LiteralMoment
import J7R43LiteralBaseline
import J9R17AllPinsAutomatic

/-! The high acquisition selectors are actually sign-independent: one
physically anchored singleton per occupied tile/order and the same
printed prefix, not just an existential list chosen after signs. -/
namespace J7R43Literal
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J6R14SpecializedBox J9R17AllPins J9R13PhysicalTables LiteralPortCompiler J9R20SameFile
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000
local instance (priority := 10000) publicZeroMachinePageEquality (a b : ℕ) :
    DecidableEq (Page a b (Fin 64)) := fun x y => Classical.propDecidable (x=y)

variable {R S V : Type} {U : V→Type}
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
variable (size C b : ℕ) (f : ℤ[X]) (ell created : ℕ)
local notation "a" => stepA (Nat.clog 2 size) 0
local notation "L" => ((2:ℕ)^a)
local notation "M" => Fintype.card (Wire R)
local notation "S₀" => printedParams (f:=f) (ell:=ell) size
local notation "∆" => sourceDelta size
variable (d : Layout (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) R S V (Fin 64) U ((2:ℕ)^(stepA (Nat.clog 2 size) 0)))
variable (F : OldTables d)
local notation "ROOT" => orientedRootCall d f ell created F
variable (mask : MaskFamily (stepA (Nat.clog 2 size) 0) b (Fin 64))
variable (wordsR : R→Fin (stepA (Nat.clog 2 size) 0)→Fin 64)
  (wordsC : S⊕V→Fin (stepA (Nat.clog 2 size) 0)→Fin 64)
variable (hC : ∀ w : Wire R, physicalCell mask (d.seat w) = declaredCell (orientedNetwork d) wordsR wordsC w)
variable (hB : Nat.card (Cell (Fin (stepA (Nat.clog 2 size) 0)) (Fin 64)) *
  (b*((2:ℕ)^(stepA (Nat.clog 2 size) 0))) ≤ 3*Nat.card (Wire R))
local notation "Q" => seatedParentPacking d mask wordsR wordsC hC hB
variable (ha : 0<stepA (Nat.clog 2 size) 0) (hu : 0<stepU (Nat.clog 2 size) 0)
  (huM : stepU (Nat.clog 2 size) 0≤Fintype.card (Wire R))
local notation "i₀" => (Fin.mk 0 ha : Fin a)
local notation "CENTER" => fun sign => extremeCenter S₀ (ROOT sign) ha hu huM
local notation "p₀" => registerPrecision S₀ (ROOT (fun _=>false)) (CENTER (fun _=>false))
local notation "W" => J9PrintedSchedule.probeCount M L
variable (ready : ∀ sign, Ready (printedParams (f:=f) (ell:=ell) size) (sourceDelta size)
  (orientedRootCall d f ell created F sign))
variable (hf : f.Monic)



set_option maxHeartbeats 12000000 in
include wordsR wordsC hC hB in
theorem public_individual_slot_machine
    (cfg : RootBounds size C f)
    (stable : ∀ sign, Stable size C (orientedRootCall d f ell created F sign))
    (hF : 0<f.natDegree) (hℓ : 0<ell) (hCreated : 0<created)
    [Fact (Irreducible (residuePoly f))]
    (e : EndpointSeating d) (he : Even L) (hL : 3≤L)
    (hr : ∀ w, rowGroup mask i₀ (d.seat w)=d.rowLabel w.1)
    (hc : ∀ w, colGroup mask i₀ (d.seat w)=actualColLabel d w)
    (hrow : ∀ r, wordsR r i₀=d.rowLabel r)
    (hpin : ∀ s, wordsC (.inl s) i₀=d.pinLabel s)
    (hold : ∀ v, wordsC (.inr v) i₀=d.colLabel v)
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (sat : ∀ v, ∃ x, satisfied (F (d.pinLabel s) v) x=true)
    (hCube : L^3≤M) (capacity : L*Fintype.card (Page a b (Fin 64))≤3*M)
    (hP : 10*M≤p₀) :
    let n := @Fintype.card (PinTile d s) (canonicalPinTile d s)
    let hPos := register_positive (ready (fun _=>false)) (CENTER (fun _=>false))
    let zero : PublicMenu mask i₀ p₀ :=
      ⟨0,J6RecursiveMenu.zero_in_menu p₀ hPos _ (fun m => m.order.val.succ_pos)⟩
    let pick : Fin n→PublicMenu mask i₀ p₀ := fun j =>
      publicAnchoredMenu d mask i₀ hr hc s off
        ⟨j.val,all_physical_orders_legal d he (by positivity) M p₀ hCube hP s j⟩
    ∀ (sign : S→Bool) (k : Fin n),
      let received := publicZeroChild size b f ell created d F Q ha hu huM ready hf sign
      let run := nativeJ7Recovery d e he F s p₀ hf hℓ
        (received zero (d.pinLabel s)) (fun j => received (pick j) (d.pinLabel s)) k
      run.answer=sign (pinEnumeration d s k).val ∧ run.work≤n*(n+1)+14*n+2 := by
  dsimp only
  intro sign k
  let hPos := register_positive (ready (fun _=>false)) (CENTER (fun _=>false))
  let zero : PublicMenu mask i₀ p₀ :=
    ⟨0,J6RecursiveMenu.zero_in_menu p₀ hPos _ (fun m => m.order.val.succ_pos)⟩
  let pick : Fin (@Fintype.card (PinTile d s) (canonicalPinTile d s))→PublicMenu mask i₀ p₀ := fun j =>
    publicAnchoredMenu d mask i₀ hr hc s off
      ⟨j.val,all_physical_orders_legal d he (by positivity) M p₀ hCube hP s j⟩
  let g := d.pinLabel s
  let idx := Fintype.equivFin (J8Physical.Wire R)
  have hNZ := centerNonzero (CENTER sign)
  have hv := extremeCenter_index S₀ ∆ (ROOT sign) (ready sign) ha hu huM
  let received := publicZeroChild size b f ell created d F Q ha hu huM ready hf sign
  have hReceipt (β : PublicMenu mask i₀ p₀) :=
    public_zero_uses_literal_child size C b f ell created d F Q ha hu huM ready hf cfg stable hF sign β g
  have hb := (hReceipt zero).trans
    (seated_baseline_integer d mask wordsR wordsC hC hB i₀ hr hc hrow hpin hold
      p₀ created F sign hf hCreated hF hℓ e he hNZ hv g)
  have hm (j : Fin (@Fintype.card (PinTile d s) (canonicalPinTile d s))) :=
    (hReceipt (pick j)).trans
      (seated_singleton_integer d mask wordsR wordsC hC hB i₀ hr hc hrow hpin hold
        p₀ created F sign hf hCreated hF hℓ e he rfl hNZ hv s off j
        (all_physical_orders_legal d he (by positivity) M p₀ hCube hP s j))
  have hDec : (fun x y : Fin 64 => LinearOrder.toDecidableEq x y) =
      (fun x y : Fin 64 => Classical.propDecidable (x=y)) := Subsingleton.elim _ _
  rw [hDec] at hb hm
  refine ⟨native_J7_recovery_correct d e he F sign s p₀ hf hℓ (received zero g)
      (fun j => received (pick j) g) k idx hL hCube capacity sat hP hF hb hm,?_⟩
  exact native_J7_recovery_work d e he F s p₀ hf hℓ (received zero g) (fun j => received (pick j) g) k

#print axioms public_individual_slot_machine
end
end J7R43Literal
