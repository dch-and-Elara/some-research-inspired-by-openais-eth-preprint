import J8R59Published
import J8R64RosterRegime
import J8R64WholeCoefficient

/-! Exact connection from the actual full-precision printed roster to
the native J8 singleton, its rational first coefficient, and all pins.
The selected valid physical file is the same as in R59. -/
namespace J8R64
open J8R59 J6R14SpecializedBox J9R17AllPins
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J9R15FrozenErasurePhysical J9R13PhysicalTables LiteralPortCompiler
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {R S V : Type} {U : V→Type}
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
local instance (priority := 10000) actualHighClassicalPageEquality (a b : ℕ) :
    DecidableEq (Page a b (Fin 64)) := fun x y => Classical.propDecidable (x=y)

set_option maxHeartbeats 7500000 in
theorem actual_all_pins_from_every_full_precision_roster
    (size C b : ℕ) (f : ℤ[X]) (ell created : ℕ)
    (d : Layout (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) R S V (Fin 64) U ((2:ℕ)^(stepA (Nat.clog 2 size) 0)))
    (F : OldTables d) (sign : S→Bool)
    (mask : MaskFamily (stepA (Nat.clog 2 size) 0) b (Fin 64))
    (wordsR : R→Fin (stepA (Nat.clog 2 size) 0)→Fin 64) (wordsC : S⊕V→Fin (stepA (Nat.clog 2 size) 0)→Fin 64)
    (hC : ∀ w : Wire R, physicalCell mask (d.seat w) = declaredCell (orientedNetwork d) wordsR wordsC w)
    (hB : Nat.card (Cell (Fin (stepA (Nat.clog 2 size) 0)) (Fin 64)) * (b*((2:ℕ)^(stepA (Nat.clog 2 size) 0))) ≤ 3*Nat.card (Wire R))
    (ha : 0<(stepA (Nat.clog 2 size) 0)) (hu : 0<((printedParams (f:=f) (ell:=ell) size)).levelWidth ((J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)).depth)
    (huM : ((printedParams (f:=f) (ell:=ell) size)).levelWidth ((J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)).depth ≤ ((J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)).edges)
    (rd : Ready (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created))
    (cfg : RootBounds size C f) (seed : Stable size C (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created))
    (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell) (hCreated : 0<created)
    [Fact (Irreducible (residuePoly f))]
    (e : EndpointSeating d) (he : Even ((2:ℕ)^(stepA (Nat.clog 2 size) 0))) (hL : 6≤((2:ℕ)^(stepA (Nat.clog 2 size) 0)))
    (hr : ∀ w : Wire R, rowGroup mask (Fin.mk 0 ha) (d.seat w)=d.rowLabel w.1)
    (hc : ∀ w : Wire R, colGroup mask (Fin.mk 0 ha) (d.seat w)=actualColLabel d w)
    (off : ∀ s, d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (sat : ∀ g v, ∃ x, satisfied (F g v) x=true)
    {M : ℕ} (idx : Wire R≃Fin M)
    (hCube : ((2:ℕ)^(stepA (Nat.clog 2 size) 0))^3≤M)
    (capacity : ((2:ℕ)^(stepA (Nat.clog 2 size) 0))*Fintype.card (Page (stepA (Nat.clog 2 size) 0) b (Fin 64))≤3*M)
    (birthBudget : created≤M) :
    let ctr := extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM
    let p := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ctr
    let sel := exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)
      (seatedParentPacking d mask wordsR wordsC hC hB)
    ∃ hp : 0<p,
    ∃ _hMenu : p+1≤Fintype.card (Probe (printedParams (f:=f) (ell:=ell) size)
      (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)),
    ∃ choices : Orders d→LiteralMenu sel rd ctr,
      (∀ w, (choices w).val.support.card=1) ∧
      Fintype.card (Orders d × Fin (p+1))=Fintype.card S*(p+1) ∧
      ∀ (B : Roster f (Probe (printedParams (f:=f) (ell:=ell) size)
          (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)))
        (pick : Fin (p+1) ↪ (Probe (printedParams (f:=f) (ell:=ell) size)
          (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created))),
      let obs (w : Orders d) := readRational p f hf (by
        letI : DecidableEq (Fin 64) := fun x y => Classical.propDecidable (x=y)
        letI : DecidableEq (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) :=
          fun x y => Classical.propDecidable (x=y)
        exact clear d (anchor d w.1) w.2)
        (highFirstFromBoxes p hp f ell hℓ (pick.trans B) (fun i => wordCompleted
          (size:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) sel rd ctr (B (pick i)) (choices w) hf))
      (∀ w, obs w = J9R18Compiled.firstCoefficient d e he F (anchor d w.1) w.2 sign) ∧
      publicAllPinDecoder d e he F obs=sign := by
  dsimp only
  let root := (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d)
    (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)
  let P₀ := printedParams (f:=f) (ell:=ell) size
  let ctr := extremeCenter P₀ root ha hu huM
  let p := registerPrecision P₀ root ctr
  let sel := exactSeatSelector P₀ (sourceDelta size) root (seatedParentPacking d mask wordsR wordsC hC hB)
  let a₀ := stepA (Nat.clog 2 size) 0
  have hCard : Fintype.card (Wire R)=M := (Fintype.card_congr idx).trans (Fintype.card_fin M)
  have hP : 10*M≤p := calc
    10*M = 10*Fintype.card (Wire R) := by rw [hCard]
    _ ≤ p := native_register_precision_ge_tenM created a₀
      (Fintype.card (Wire R)) (stepU (Nat.clog 2 size) 0) ctr.val ha
  have hp : 0<p := register_positive rd ctr
  have hMenu : p+1≤Fintype.card (Probe P₀ root) :=
    actual_printed_root_full_precision_fits cfg root ctr rfl (by exact birthBudget.trans_eq hCard.symm) huM
  have hOrd (s : S) (n : Fin (@Fintype.card (PinTile d s) (canonicalPinTile d s))) :
      n.val<p-1 := all_physical_orders_legal d he (by positivity) M p hCube hP s n
  have point (w : Orders d) :=
    literal_same_center_anchored_singleton size C b f ell created d F sign mask wordsR wordsC hC hB
      ha hu huM rd cfg seed hf hF hℓ hCreated e he (by omega) hr hc (anchor d w.1) (off _) w.2
      (hOrd _ w.2) idx
  choose choice hOne hObs using point
  have count : Fintype.card (Orders d × Fin (p+1))=Fintype.card S*(p+1) := by
    rw [Fintype.card_prod,moment_orders_count,Fintype.card_fin]
  refine ⟨hp,hMenu,choice,hOne,count,?_⟩
  intro B pick
  let recv (w : Orders d) (i : Fin (p+1)) : Box f ell p :=
    wordCompleted (size:=size) (c:=root) sel rd ctr (B (pick i)) (choice w) hf
  let obs (w : Orders d) : ℚ := readRational p f hf (by
    letI : DecidableEq (Fin 64) := fun x y => Classical.propDecidable (x=y)
    letI : DecidableEq (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) :=
      fun x y => Classical.propDecidable (x=y)
    exact clear d (anchor d w.1) w.2)
    (highFirstFromBoxes p hp f ell hℓ (pick.trans B) (recv w))
  change (∀ w,obs w=J9R18Compiled.firstCoefficient d e he F (anchor d w.1) w.2 sign) ∧
    publicAllPinDecoder d e he F obs=sign
  let pageFinite : Fintype (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := inferInstance
  letI : DecidableEq (Fin 64) := fun x y => Classical.propDecidable (x=y)
  letI : Fintype (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := pageFinite
  letI : DecidableEq (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) :=
    fun x y => Classical.propDecidable (x=y)
  have hCoeff (w : Orders d) : obs w =
      physicalCoeff d e he (anchor d w.1) F sign (fun _ _ _ _=>0) w.2 (fun _=>0) := by
    let s := anchor d w.1
    have small : 2<(2:ℕ)^a₀ := by exact (by decide : 2<6).trans_le hL
    have hRead := full_precision_signed_first_from_grouped_boxes d e he small a₀ rfl s (off s)
      idx hCube capacity F sign
      (fun g v r k => (genuineBase d a₀ g v r k).divX) (fun _ _ _ _=>0) w.2
      (fun x => (genuineCross d a₀ p w.2.val he small s x).divX) (fun _=>0)
      p ell hp hP hℓ f hf hF (pick.trans B) (recv w) (fun i => hObs w (B (pick i)))
    exact hRead
  refine ⟨?_,publicAllPinDecoder_exact d e he (by omega) F sign off sat obs hCoeff⟩
  intro w
  exact (hCoeff w).trans ((J9R18Compiled.firstCoefficient_exact d e he F (anchor d w.1)
    w.2 sign (fun _ _ _ _=>0) (fun _=>0)).symm)

#print axioms actual_all_pins_from_every_full_precision_roster
end
end J8R64