import J8RelaxedBinding
import J8RelaxedReceipt
import J9R20SameFileHighAnchors
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000
namespace J8Physical.Relaxed
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J6R14SpecializedBox J9R17AllPins J9R13PhysicalTables LiteralPortCompiler J9R20SameFile
noncomputable section
local instance (priority := 10000) relaxedPublicAnchorPageEquality (a b : ℕ) :
    DecidableEq (Page a b (Fin 64)) := fun x y => Classical.propDecidable (x=y)
section Tile
variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
set_option maxHeartbeats 2700000 in
theorem chart_first_equals_physical_coeff
    (e : RowEndpointSeating d) (he : Even L) (hL : 2<L) (k : ℕ) (hpow : L=2^k)
    (a : S) (off : d.rowLabel (pinWire d a).1≠d.pinLabel a)
    (idx : Wire R≃Fin M) (F : OldTables d) (sign : S→Bool)
    (tail : IntegralArguments d) (higher : RestArguments d)
    (n : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a→Source[X])
    (rest : TargetPorts d a→ℚ[X])
    (rows : (Fin M→Bool)→R→Bool→ℚ[X]) (cross : Fin L→ℚ[X]) (source : (Fin M→Bool)→ℚ[X]) :
    (J9End.literalCompleted (J9End.chart d a idx (satisfied (globalCNF d idx F sign)))
      n rows cross source).coeff 1 =
      physicalCoeff d e he a F sign higher n rest := by
  exact (exactFirst_from_seated_children d e he hL a off idx F sign tail n kt k hpow rows cross source).symm.trans
    (physical_first_derived d e he hL a off idx F sign tail higher n kt rest k hpow)


end Tile
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
theorem same_public_high_decodes_all_signs
    (cfg : RootBounds size C f)
    (stable : ∀ sign, Stable size C (orientedRootCall d f ell created F sign))
    (hF : 0<f.natDegree) (hℓ : 0<ell) (hCreated : 0<created)
    [Fact (Irreducible (residuePoly f))]
    (e : RowEndpointSeating d) (he : Even L) (hL : 3≤L)
    (hr : ∀ w : Wire R, rowGroup mask i₀ (d.seat w)=d.rowLabel w.1)
    (hc : ∀ w : Wire R, colGroup mask i₀ (d.seat w)=actualColLabel d w)
    (off : ∀ s, d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (sat : ∀ g v, ∃ x, satisfied (F g v) x=true)
    (hCube : L^3≤M) (capacity : L*Fintype.card (Page a b (Fin 64))≤3*M)
    (hP : 10*M≤p₀) (hMenu : 10*M+1≤W) :
    let hM : 0<M := (show 0<L^3 by positivity).trans_le hCube
    let fit := hMenu.trans (ready (fun _=>false)).fit
    let pick : Orders d → PublicMenu mask i₀ p₀ := fun w =>
      publicAnchoredMenu d mask i₀ hr hc (anchor d w.1) (off _)
        ⟨w.2.val, all_physical_orders_legal d he (by positivity) M p₀ hCube hP _ w.2⟩
    (∀ w, (pick w).val.support.card=1) ∧
    ∀ sign : S→Bool, publicAllPinDecoder d e he F (fun w =>
      publicCoefficient d (anchor d w.1) (Fintype.equivFin (Wire R)) w.2 p₀ ell hP hℓ f hf fit hM
        (fun j => publicHighObservation size b f ell created d F Q ha hu huM ready hf sign
          (Fin.castLE hMenu j) (pick w))) = sign := by
  dsimp only
  constructor
  · intro w
    exact public_anchored_support d mask i₀ hr hc _ _ _
  · intro sign
    refine publicAllPinDecoder_exact d e he (by omega) F sign off sat _ ?_
    intro w
    let idx := Fintype.equivFin (Wire R)
    let s := anchor d w.1
    let n := w.2
    let hon := all_physical_orders_legal d he (by positivity) M p₀ hCube hP s n
    let mode := publicAnchoredMenu d mask i₀ hr hc s (off s) ⟨n.val,hon⟩
    let fit := hMenu.trans (ready (fun _=>false)).fit
    let hM : 0<M := (show 0<L^3 by positivity).trans_le hCube
    let recv (j : Fin (10*M+1)) : Box f ell p₀ :=
      publicHighObservation size b f ell created d F Q ha hu huM ready hf sign (Fin.castLE hMenu j) mode
    have read := publicCoefficient_exact_formula d s idx n p₀ ell hP hℓ f hf fit hM
      recv (satisfied (globalCNF d idx F sign))
    have lowL : 2<L := by omega
    let pageFinite : Fintype (Page a b (Fin 64)) := inferInstance
    letI : DecidableEq (Fin 64) := fun x y=>Classical.propDecidable (x=y)
    letI : Fintype (Page a b (Fin 64)) := pageFinite
    letI : DecidableEq (Page a b (Fin 64)) := fun x y=>Classical.propDecidable (x=y)
    have bridge := signed_first_from_verified_receipts d e he hL a rfl s (off s) idx hCube capacity F sign
      (fun g v rr k => (genuineBase d a g v rr k).divX) n
      (fun x => (genuineCross d a p₀ n.val he lowL s x).divX)
      (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) p₀ ell hP hℓ f hf hF fit recv
    have sound : _ := bridge (by
      intro j
      have hp := register_positive (ready sign) (CENTER sign)
      let z := Fin.castLE hMenu j
      have receipt := public_high_uses_literal_projection size C b f ell created d F Q
        ha hu huM ready hf cfg stable hF sign z mode
      have bound := seated_actual_children_high_observation d mask wordsR wordsC hC hB i₀ rfl hr hc
        (centerNonzero (CENTER sign)) (extremeCenter_index S₀ ∆ (ROOT sign) (ready sign) ha hu huM)
        e he lowL p₀ ell created f hf hp hCreated hF hℓ s (off s) n hon F sign idx
        (chosenRep f.natDegree _ (ready sign).fit z)
      have addr := literal_address_at_sample S₀ ∆ (ROOT sign) (ready sign) (CENTER sign) z
      rw [addr] at receipt
      have pref :
          chosenRep f.natDegree (J9PrintedSchedule.probeCount (ROOT sign).edges
            (2^(S₀).levelBits (ROOT sign).depth)) (ready sign).fit z =
          chosenRep f.natDegree (10*M+1) fit j :=
        printed_probe_prefix f.natDegree _ (10*M+1) hMenu (ready sign).fit fit j
      exact (receipt.trans bound).trans (by rw [pref]))
    have phys := chart_first_equals_physical_coeff d e he lowL a rfl s (off s) idx F sign
      (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) n (fun _ => 0) (fun _ => 0)
      (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0)
    exact read.trans (sound.trans phys)

#print axioms chart_first_equals_physical_coeff
#print axioms same_public_high_decodes_all_signs
end
end J8Physical.Relaxed