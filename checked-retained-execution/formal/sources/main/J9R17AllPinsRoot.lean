import J6R16SpecializedBoxSignedExpanded
import J9R17AllPinsDecode

/-! Actual source acquisition at all occupied printed tiles. The
returned bit vector is decoded with only the public chart. No
unmetered callback supplies the moment coefficients. -/
namespace J9R17AllPins
open J6R14SpecializedBox
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J9R15FrozenErasurePhysical J9R13PhysicalTables LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false

variable {R S V : Type} {U : V→Type} 
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
local instance (priority := 10000) classicalPageEquality (a b : ℕ) :
    DecidableEq (Page a b (Fin 64)) := fun x y => Classical.propDecidable (x=y)

set_option maxHeartbeats 4300000 in
theorem all_pins_from_literal_recursive_receipts
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
    (e : EndpointSeating d) (he : Even ((2:ℕ)^(stepA (Nat.clog 2 size) 0))) (hL : 3≤((2:ℕ)^(stepA (Nat.clog 2 size) 0)))
    (hr : ∀ w : Wire R, rowGroup mask (Fin.mk 0 ha) (d.seat w)=d.rowLabel w.1)
    (hc : ∀ w : Wire R, colGroup mask (Fin.mk 0 ha) (d.seat w)=actualColLabel d w)
    (off : ∀ s, d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (sat : ∀ g v, ∃ x, satisfied (F g v) x=true)
    (ordersLegal : ∀ (s : S) (n : Fin (@Fintype.card (PinTile d s) (canonicalPinTile d s))),
      n.val<registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)
        (extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM)-1)
    {M : ℕ} (idx : Wire R≃Fin M)
    (hCube : ((2:ℕ)^(stepA (Nat.clog 2 size) 0))^3≤M) (capacity : ((2:ℕ)^(stepA (Nat.clog 2 size) 0))*Fintype.card (Page (stepA (Nat.clog 2 size) 0) b (Fin 64))≤3*M)
    (hP : 10*M≤registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM))
    (hMenu : 10*M+1≤J9PrintedSchedule.probeCount (Fintype.card (Wire R)) ((2:ℕ)^(stepA (Nat.clog 2 size) 0))) :
    let ctr := extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM
    let p := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ctr
    let sel := exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)
      (seatedParentPacking d mask wordsR wordsC hC hB)
    ∃ choices : Orders d→Fin (10*M+1)→LiteralMenu sel rd ctr,
      (∀ w i, (choices w i).val.support.card=1) ∧
      let fit := hMenu.trans rd.fit
      let mPos : 0<M := (show 0<((2:ℕ)^(stepA (Nat.clog 2 size) 0))^3 by positivity).trans_le hCube
      (publicAllPinDecoder d e he F (fun w => publicCoefficient d (anchor d w.1) idx w.2 p ell
        hP hℓ f hf fit mPos (fun i => printedPacketProduct
          (s:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) sel rd ctr (Fin.castLE hMenu i) (choices w i) hf))) = sign := by
  dsimp only
  let ctr := extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM
  let p := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ctr
  let sel := exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)
    (seatedParentPacking d mask wordsR wordsC hC hB)
  have mPos : 0<M := (show 0<((2:ℕ)^(stepA (Nat.clog 2 size) 0))^3 by positivity).trans_le hCube
  have point (w : Orders d) :=
    literal_recursive_receipts_signed_first size C b f ell created d F sign mask wordsR wordsC hC hB
      ha hu huM rd cfg seed hf hF hℓ hCreated e he hL hr hc (anchor d w.1) (off _) w.2
      (ordersLegal _ w.2) idx hCube capacity (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) hP hMenu
  choose choice hOne hRead using point
  refine ⟨choice,hOne,?_⟩
  refine publicAllPinDecoder_exact d e he (by omega) F sign off sat _ ?_
  intro w
  let a := anchor d w.1
  let recvd (i : Fin (10*M+1)) : Box f ell p :=
    printedPacketProduct (s:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) sel rd ctr (Fin.castLE hMenu i) (choice w i) hf
  have C := publicCoefficient_exact_formula d a idx w.2 p ell hP hℓ f hf (hMenu.trans rd.fit) mPos
    recvd (satisfied (globalCNF d idx F sign))
  have P := chart_first_equals_physical_coeff d e he (show 2<((2:ℕ)^(stepA (Nat.clog 2 size) 0)) by omega)
    (stepA (Nat.clog 2 size) 0) rfl a (off a) idx F sign (fun _ _ _ _ => 0) (fun _ _ _ _ => 0)
    w.2 (fun _ => 0) (fun _ => 0) (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0)
  exact C.trans ((hRead w).trans P)

#print axioms all_pins_from_literal_recursive_receipts
end
end J9R17AllPins