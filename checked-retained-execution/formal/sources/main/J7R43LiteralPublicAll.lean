
import J9R20SameFileHighAnchors
import J7R43LiteralPublicZero
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
local instance (priority := 10000) publicZeroPageEquality (a b : ℕ) :
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


include wordsR wordsC hC hB in
set_option maxHeartbeats 14000000 in
theorem same_public_zero_decodes_all_signs
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
    (off : ∀ s, d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (sat : ∀ g v, ∃ x, satisfied (F g v) x=true)
    (hCube : L^3≤M) (capacity : L*Fintype.card (Page a b (Fin 64))≤3*M)
    (hP : 10*M≤p₀) :
    ∃ (zero : PublicMenu mask i₀ p₀) (pick : Orders d→PublicMenu mask i₀ p₀),
      zero.val=0 ∧ (∀ w, (pick w).val.support.card=1) ∧
      ∀ sign : S→Bool,
        let received := publicZeroChild size b f ell created d F Q ha hu huM ready hf sign
        let recover := fun k : Occupied d =>
          let s := anchor d k
          NativeMomentReconstruction.decodeBits (coordinates d s)
            (fun _ => (readUnsigned p₀ hf hℓ (received zero (d.pinLabel s)) : ℚ))
            (fun b => actualPublicMoment d e he F s b.val)
            (fun b => (readUnsigned p₀ hf hℓ (received (pick ⟨k,b⟩) (d.pinLabel s)) : ℚ))
        (fun s => recover ((orderPin d).symm s).1 ((orderPin d).symm s).2) = sign := by
  let hPos := register_positive (ready (fun _=>false)) (CENTER (fun _=>false))
  let zero : PublicMenu mask i₀ p₀ :=
    ⟨0,J6RecursiveMenu.zero_in_menu p₀ hPos _ (fun m => m.order.val.succ_pos)⟩
  let pick : Orders d→PublicMenu mask i₀ p₀ := fun w =>
    publicAnchoredMenu d mask i₀ hr hc (anchor d w.1) (off _)
      ⟨w.2.val,all_physical_orders_legal d he (by positivity) M p₀ hCube hP _ w.2⟩
  refine ⟨zero,pick,rfl,(fun w => public_anchored_support d mask i₀ hr hc _ _ _),?_⟩
  intro sign
  let recv := publicZeroChild size b f ell created d F Q ha hu huM ready hf sign
  let readTile (k : Occupied d) :
      Fin (@Fintype.card (PinTile d (anchor d k)) (canonicalPinTile d (anchor d k))) → Bool :=
    let s := anchor d k
    NativeMomentReconstruction.decodeBits (coordinates d s)
      (fun _ => (readUnsigned p₀ hf hℓ (recv zero (d.pinLabel s)) : ℚ))
      (fun b => actualPublicMoment d e he F s b.val)
      (fun b => (readUnsigned p₀ hf hℓ (recv (pick ⟨k,b⟩) (d.pinLabel s)) : ℚ))
  refine all_bits_from_decoded_individual_tiles d readTile sign ?_
  intro k j
  let s := anchor d k
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
  have hm (n : Fin (@Fintype.card (PinTile d s) (canonicalPinTile d s))) :=
    (hReceipt (pick ⟨k,n⟩)).trans
      (seated_singleton_integer d mask wordsR wordsC hC hB i₀ hr hc hrow hpin hold
        p₀ created F sign hf hCreated hF hℓ e he rfl hNZ hv s (off s) n
        (all_physical_orders_legal d he (by positivity) M p₀ hCube hP s n))
  have hDec : (fun x y : Fin 64 => LinearOrder.toDecidableEq x y) =
      (fun x y : Fin 64 => Classical.propDecidable (x=y)) := Subsingleton.elim _ _
  rw [hDec] at hb hm
  have decoded := decoded_from_actual_child_residues d e he F sign s idx hL hCube capacity
    (sat g) p₀ hP hf hF hℓ (received zero g) (fun n => received (pick ⟨k,n⟩) g) hb hm
  exact congrFun decoded j

#print axioms same_public_zero_decodes_all_signs
end
end J7R43Literal
