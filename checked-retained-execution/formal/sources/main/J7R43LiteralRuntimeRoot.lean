import J7R43LiteralBaseline
import J7R43LiteralAllowedZero
import J6R16SpecializedBoxRoot

/-! The paper's admitted zero probe at the printed extreme centre gives
separate runtime receipts for the baseline and each source moment.
The selected parent uses precisely the supplied original seats. -/
namespace J7R43Literal
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted J6R11Integral
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler J6R14SpecializedBox
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxRecDepth 5000

variable {R S V : Type} {U : V→Type} {size C b : ℕ}
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
variable (f : ℤ[X]) (ell created : ℕ)
local notation "S₀" => (printedParams (f:=f) (ell:=ell) size)
private def levelBitsRoot (f : ℤ[X]) (ell size : ℕ) : ℕ := (printedParams (f:=f) (ell:=ell) size).levelBits 0
local notation "A₀" => (levelBitsRoot f ell size)
local notation "L₀" => (2^A₀:ℕ)
variable (d : Layout (Page (levelBitsRoot f ell size) b (Fin 64)) R S V (Fin 64) U (2^(levelBitsRoot f ell size):ℕ))
variable (F : OldTables d) (sign : S→Bool)
local notation "r₀" => (orientedRootCall d f ell created F sign)
variable (mask : MaskFamily (levelBitsRoot f ell size) b (Fin 64))
variable (wordsR : R→Fin (levelBitsRoot f ell size)→Fin 64) (wordsC : S⊕V→Fin (levelBitsRoot f ell size)→Fin 64)
variable (hC : ∀ w : Wire R, physicalCell mask (d.seat w) =
  declaredCell (orientedNetwork d) wordsR wordsC w)
variable (hB : Nat.card (Cell (Fin (levelBitsRoot f ell size)) (Fin 64)) * (b*(2^(levelBitsRoot f ell size):ℕ)) ≤ 3*Nat.card (Wire R))
local notation "Q₀" => (seatedParentPacking d mask wordsR wordsC hC hB)
local notation "sel₀" => (exactSeatSelector S₀ (sourceDelta size) r₀ Q₀)
variable (ha : 0<(levelBitsRoot f ell size)) (hu : 0<((printedParams (f:=f) (ell:=ell) size)).levelWidth ((orientedRootCall d f ell created F sign)).depth)
variable (huM : ((printedParams (f:=f) (ell:=ell) size)).levelWidth ((orientedRootCall d f ell created F sign)).depth ≤ ((orientedRootCall d f ell created F sign)).edges)
local notation "t₀" => (extremeCenter S₀ r₀ ha hu huM)
variable (rd : Ready (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (orientedRootCall d f ell created F sign))
local notation "p₀" => (registerPrecision S₀ r₀ t₀)
local notation "i₀" => (centerIndex (S:=S₀) (Δ:=sourceDelta size) (c:=r₀) rd t₀)
local notation "aR" => (packing (S:=S₀) (Δ:=sourceDelta size) (c:=r₀) sel₀ rd)
variable (cfg : RootBounds size C f) (seed : Stable size C (orientedRootCall d f ell created F sign))
variable (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell) (hCreated : 0<created)
variable [Fact (Irreducible (residuePoly f))]
variable (e : EndpointSeating d) (even : Even (2^(levelBitsRoot f ell size):ℕ))
variable (hr : ∀ w : Wire R, rowGroup mask (Fin.mk 0 ha) (d.seat w)=d.rowLabel w.1)
variable (hc : ∀ w : Wire R, colGroup mask (Fin.mk 0 ha) (d.seat w)=actualColLabel d w)
variable (hrow : ∀ r, wordsR r (Fin.mk 0 ha) = d.rowLabel r)
variable (hpin : ∀ s, wordsC (.inl s) (Fin.mk 0 ha) = d.pinLabel s)
variable (hold : ∀ v, wordsC (.inr v) (Fin.mk 0 ha) = d.colLabel v)
local notation "file" => (orientedEntryFile d f ell created F sign)

set_option maxHeartbeats 6000000 in
include cfg seed hF hℓ hCreated hr hc hrow hpin hold in
theorem allowed_zero_one_baseline (g : Fin 64) :
    ∃ β : LiteralMenu (S:=S₀) (Δ:=sourceDelta size) (c:=r₀) sel₀ rd t₀,
      β.val=0 ∧
      allowedZeroValue (s:=size) (c:=r₀) sel₀ rd t₀ β g hf =
        (J8J9Grouped.child d e even F sign g none (fun _ => 1) : Box f ell p₀) := by
  have hi : i₀ = Fin.mk 0 ha :=
    Fin.ext (extremeCenter_index S₀ (sourceDelta size) r₀ rd ha hu huM)
  have hr' : ∀ w, rowGroup mask i₀ (d.seat w)=d.rowLabel w.1 := by simpa only [hi] using hr
  have hc' : ∀ w, colGroup mask i₀ (d.seat w)=actualColLabel d w := by simpa only [hi] using hc
  have hrh : ∀ r, wordsR r i₀=d.rowLabel r := by simpa only [hi] using hrow
  have hph : ∀ s, wordsC (.inl s) i₀=d.pinLabel s := by simpa only [hi] using hpin
  have hoh : ∀ v, wordsC (.inr v) i₀=d.colLabel v := by simpa only [hi] using hold
  let β : LiteralMenu (S:=S₀) (Δ:=sourceDelta size) (c:=r₀) sel₀ rd t₀ :=
    ⟨0,J6RecursiveMenu.zero_in_menu p₀ (register_positive rd t₀) _
      (fun m => m.order.val.succ_pos)⟩
  refine ⟨β,rfl,?_⟩
  have hreal := allowed_zero_actual_run (s:=size) (c:=r₀) cfg sel₀ rd t₀ β g seed hf hF
  have eqPack : aR=Q₀ := exactSeatSelector_at_root S₀ (sourceDelta size) r₀ Q₀ rd
  have hobs : ∀ q : PhysicalPacking (orientedNetwork d) A₀ (Fin 64), q=Q₀ →
      reduce p₀ f ell (actualChildTruth q i₀ (centerNonzero t₀) rfl p₀
        0 file hf 0 g) =
      (J8J9Grouped.child d e even F sign g none (fun _ => 1) : Box f ell p₀) := by
    intro q hq
    subst q
    exact seated_baseline_integer d mask wordsR wordsC hC hB i₀ hr' hc' hrh hph hoh p₀ created
      F sign hf hCreated hF hℓ e even (centerNonzero t₀) rfl g
  exact hreal.trans (hobs aR eqPack)

#print axioms allowed_zero_one_baseline
end
end J7R43Literal
