import J7R43LiteralRuntimeEval
import J7R43LiteralPortableDecode
import J6R16SpecializedBoxBounds

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

local instance (priority := 15000) j7PageEqRuntimePortable (a b : ℕ) :
    DecidableEq (Page a b (Fin 64)) := fun x y => Classical.propDecidable (x=y)

variable {R S V : Type} {U : V→Type} {size C b : ℕ}
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
variable (f : ℤ[X]) (ell created : ℕ)
local notation "S₀" => (printedParams (f:=f) (ell:=ell) size)
private def levelBitsPortRoot (f : ℤ[X]) (ell size : ℕ) : ℕ := (printedParams (f:=f) (ell:=ell) size).levelBits 0
local notation "A₀" => (levelBitsPortRoot f ell size)
local notation "L₀" => (2^A₀:ℕ)
variable (d : Layout (Page (levelBitsPortRoot f ell size) b (Fin 64)) R S V (Fin 64) U (2^(levelBitsPortRoot f ell size):ℕ))
variable (F : OldTables d) (sign : S→Bool)
local notation "r₀" => (orientedRootCall d f ell created F sign)
variable (mask : MaskFamily (levelBitsPortRoot f ell size) b (Fin 64))
variable (wordsR : R→Fin (levelBitsPortRoot f ell size)→Fin 64) (wordsC : S⊕V→Fin (levelBitsPortRoot f ell size)→Fin 64)
variable (hC : ∀ w : Wire R, physicalCell mask (d.seat w) =
  declaredCell (orientedNetwork d) wordsR wordsC w)
variable (hB : Nat.card (Cell (Fin (levelBitsPortRoot f ell size)) (Fin 64)) * (b*(2^(levelBitsPortRoot f ell size):ℕ)) ≤ 3*Nat.card (Wire R))
local notation "Q₀" => (seatedParentPacking d mask wordsR wordsC hC hB)
local notation "sel₀" => (exactSeatSelector S₀ (sourceDelta size) r₀ Q₀)
variable (ha : 0<(levelBitsPortRoot f ell size)) (hu : 0<((printedParams (f:=f) (ell:=ell) size)).levelWidth ((orientedRootCall d f ell created F sign)).depth)
variable (huM : ((printedParams (f:=f) (ell:=ell) size)).levelWidth ((orientedRootCall d f ell created F sign)).depth ≤ ((orientedRootCall d f ell created F sign)).edges)
local notation "t₀" => (extremeCenter S₀ r₀ ha hu huM)
variable (rd : Ready (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (orientedRootCall d f ell created F sign))
local notation "p₀" => (registerPrecision S₀ r₀ t₀)
local notation "i₀" => (centerIndex (S:=S₀) (Δ:=sourceDelta size) (c:=r₀) rd t₀)
local notation "aR" => (packing (S:=S₀) (Δ:=sourceDelta size) (c:=r₀) sel₀ rd)
variable (cfg : RootBounds size C f) (seed : Stable size C (orientedRootCall d f ell created F sign))
variable (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell) (hCreated : 0<created)
variable [Fact (Irreducible (residuePoly f))]
variable (e : EndpointSeating d) (even : Even (2^(levelBitsPortRoot f ell size):ℕ))
variable (hr : ∀ w : Wire R, rowGroup mask (Fin.mk 0 ha) (d.seat w)=d.rowLabel w.1)
variable (hc : ∀ w : Wire R, colGroup mask (Fin.mk 0 ha) (d.seat w)=actualColLabel d w)
variable (hrow : ∀ r, wordsR r (Fin.mk 0 ha) = d.rowLabel r)
variable (hpin : ∀ s, wordsC (.inl s) (Fin.mk 0 ha) = d.pinLabel s)
variable (hold : ∀ v, wordsC (.inr v) (Fin.mk 0 ha) = d.colLabel v)
local notation "file" => (orientedEntryFile d f ell created F sign)

set_option maxHeartbeats 7500000 in
include cfg seed hF hℓ hCreated hr hc hrow hpin hold in
theorem allowed_zero_source_evaluator_decodes_tile
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    {M : ℕ} (idx : Wire R≃Fin M) (hL : 3≤L₀) (hM : L₀^3≤M)
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x=true) :
    ∃ mode : Fin (Nat.card (PinTile d s)) →
          LiteralMenu (S:=S₀) (Δ:=sourceDelta size) (c:=r₀) sel₀ rd t₀,
      (∀ order, (mode order).val.support.card=1) ∧
      decodeNativeNaturalOrders d e even F s p₀ hf hℓ
        (integerBaseline d e even F (d.pinLabel s))
        (fun order => allowedZeroValue (s:=size) (c:=r₀) sel₀ rd t₀ (mode order) (d.pinLabel s) hf) =
          fun j => sign (pinAtNaturalIndex d s j) := by
  have cardW : Fintype.card (Wire R)=M := (Fintype.card_congr idx).trans (Fintype.card_fin _)
  have hp : 10*M≤p₀ := by
    rw [← cardW]
    exact native_register_precision_ge_tenM (r₀).prec A₀ (r₀).edges
      ((S₀).levelWidth (r₀).depth) (t₀).val ha
  have capacity : L₀*Fintype.card (Page A₀ b (Fin 64))≤3*M := by
    have hh := physical_packet_count Q₀
    change Nat.card (Page A₀ b (Fin 64))*L₀≤3*Nat.card (Wire R) at hh
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,cardW,Nat.mul_comm] at hh
    exact hh
  have hTile : Nat.card (PinTile d s) ≤ L₀/2 := by
    calc
      Nat.card (PinTile d s) = @Fintype.card (PinTile d s) (canonicalPinTile d s) :=
        @Nat.card_eq_fintype_card (PinTile d s) (canonicalPinTile d s)
      _ ≤ L₀/2 := pins_per_tile d s even
  have hGood (n : Fin (Nat.card (PinTile d s))) : n.val<p₀-1 := by
    have hh : L₀≤L₀^3 := by
      simpa only [pow_one] using (Nat.pow_le_pow_right (by omega : 0<L₀) (by decide : 1≤(3:ℕ)))
    have hle := hh.trans hM
    have hb := n.isLt
    omega
  have H (n : Fin (Nat.card (PinTile d s))) := allowed_zero_one_source_eval
    (f:=f) (ell:=ell) (size:=size) (C:=C) (b:=b) created d F sign mask wordsR wordsC hC hB
    ha hu huM rd cfg seed hf hF hℓ hCreated e even hr hc hrow hpin hold s off n.val n.isLt (hGood n) sat
  choose m legal hsample using H
  exact ⟨m,legal,decode_from_integer_evaluator_residues d e even F sign s idx hL hM capacity sat
    p₀ hp hf hF hℓ _ _ rfl hsample⟩

#print axioms allowed_zero_source_evaluator_decodes_tile
end
end J7R43Literal