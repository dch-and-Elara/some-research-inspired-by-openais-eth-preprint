import J8R59PhysicalReceipts
import J8R59SignedReceipt
import J9R18CompiledReadout

/-! Same physical Appendix D pin file and extreme positive center, arbitrary legal source words, and the public signed decoder. A fixed legal singleton per tile/order is used at every word. This is a completed-slot interface, not a fee bound for separately acquiring the slots. -/
namespace J8R59
open J6R14SpecializedBox J9R17AllPins
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
theorem same_singletons_for_all_rosters_and_joint_readout
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
    :
    let ctr := extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM
    let p := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ctr
    let sel := exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)
      (seatedParentPacking d mask wordsR wordsC hC hB)
    ∃ choices : Orders d→LiteralMenu sel rd ctr,
      (∀ w, (choices w).val.support.card=1) ∧
      ∀ W : Roster f (Fin (10*M+1)),
      let mPos : 0<M := (show 0<((2:ℕ)^(stepA (Nat.clog 2 size) 0))^3 by positivity).trans_le hCube
      let obs (w : Orders d) := publicCoefficientAtRoster d (anchor d w.1) idx w.2 p ell
        hP hℓ f hf W mPos (fun i => wordCompleted
          (size:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) sel rd ctr (W i) (choices w) hf)
      (∀ w, obs w = J9R18Compiled.firstCoefficient d e he F (anchor d w.1) w.2 sign) ∧
      publicAllPinDecoder d e he F obs = sign := by
  dsimp only
  let ctr := extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM
  let p := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ctr
  let sel := exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)
    (seatedParentPacking d mask wordsR wordsC hC hB)
  have mPos : 0<M := (show 0<((2:ℕ)^(stepA (Nat.clog 2 size) 0))^3 by positivity).trans_le hCube
  have point (w : Orders d) :=
    literal_same_center_anchored_singleton size C b f ell created d F sign mask wordsR wordsC hC hB
      ha hu huM rd cfg seed hf hF hℓ hCreated e he (by omega) hr hc (anchor d w.1) (off _) w.2
      (ordersLegal _ w.2) idx
  choose choice hOne hObs using point
  refine ⟨choice,hOne,?_⟩
  intro W
  let obs (w : Orders d) : ℚ := publicCoefficientAtRoster d (anchor d w.1) idx w.2 p ell
    hP hℓ f hf W mPos (fun i =>
      wordCompleted (size:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) sel rd ctr (W i) (choice w) hf)
  let pageFinite : Fintype (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := inferInstance
  letI : DecidableEq (Fin 64) := fun x y => Classical.propDecidable (x=y)
  letI : Fintype (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := pageFinite
  letI : DecidableEq (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) :=
    fun x y => Classical.propDecidable (x=y)
  have hCoeff (w : Orders d) : obs w =
      physicalCoeff d e he (anchor d w.1) F sign (fun _ _ _ _ => 0) w.2 (fun _ => 0) := by
    let a := anchor d w.1
    let recvd (i : Fin (10*M+1)) : Box f ell p :=
      wordCompleted (size:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) sel rd ctr (W i) (choice w) hf
    have C := publicCoefficientAtRoster_exact_formula d a idx w.2 p ell hP hℓ f hf W mPos
      recvd (satisfied (globalCNF d idx F sign))
    have P := chart_first_equals_physical_coeff d e he (show 2<((2:ℕ)^(stepA (Nat.clog 2 size) 0)) by omega)
      (stepA (Nat.clog 2 size) 0) rfl a (off a) idx F sign (fun _ _ _ _ => 0) (fun _ _ _ _ => 0)
      w.2 (fun _ => 0) (fun _ => 0) (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0)
    have hk : 2<2^(stepA (Nat.clog 2 size) 0) := by omega
    have hRead := signed_first_from_arbitrary_receipts d e he hL
      (stepA (Nat.clog 2 size) 0) rfl a (off a) idx hCube capacity F sign
      (fun g v r k => (genuineBase d (stepA (Nat.clog 2 size) 0) g v r k).divX)
      w.2 (fun j => (genuineCross d (stepA (Nat.clog 2 size) 0) p w.2.val he hk a j).divX)
      (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) p ell hP hℓ f hf hF W recvd
      (fun i => hObs w (W i))
    exact C.trans (hRead.trans P)
  refine ⟨?_, publicAllPinDecoder_exact d e he (by omega) F sign off sat obs hCoeff⟩
  intro w
  exact (hCoeff w).trans ((J9R18Compiled.firstCoefficient_exact d e he F (anchor d w.1)
    w.2 sign (fun _ _ _ _ => 0) (fun _ => 0)).symm)

#print axioms same_singletons_for_all_rosters_and_joint_readout
end
end J8R59