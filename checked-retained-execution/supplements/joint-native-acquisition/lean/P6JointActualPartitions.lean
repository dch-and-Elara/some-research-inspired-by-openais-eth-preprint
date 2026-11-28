import P6JointActual
import P6JointPartition

namespace P6Joint
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J8R59 J6R14SpecializedBox J9R15FrozenErasurePhysical
noncomputable section
set_option linter.unusedSectionVars false

variable {R S V : Type} {U : V→Type} 
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
set_option maxHeartbeats 4000000 in
theorem actual_singleton_eq_partitions
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
    (e : EndpointSeating d) (he : Even ((2:ℕ)^(stepA (Nat.clog 2 size) 0))) (hL : 2<((2:ℕ)^(stepA (Nat.clog 2 size) 0)))
    (hr : ∀ w : Wire R, rowGroup mask (Fin.mk 0 ha) (d.seat w)=d.rowLabel w.1)
    (hc : ∀ w : Wire R, colGroup mask (Fin.mk 0 ha) (d.seat w)=actualColLabel d w)
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (n : Fin (@Fintype.card (PinTile d s) (canonicalPinTile d s))) (hN : n.val<registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM)-1)
    {M : ℕ} (idx : Wire R≃Fin M) :
    let t₀ := extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM
    let p₀ := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) t₀
    ∃ β : LiteralMenu (exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (seatedParentPacking d mask wordsR wordsC hC hB)) rd t₀, β.val.support.card=1 ∧
      ∀ adr : Fin f.natDegree → Bool,
      wordCompleted (size:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) (exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (seatedParentPacking d mask wordsR wordsC hC hB)) rd t₀ adr β hf =
      J6ActiveInterpolation.scalarIn p₀ f ell (by
        letI : DecidableEq (Fin 64) := fun x y => Classical.propDecidable (x=y)
        letI : DecidableEq (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := fun x y => Classical.propDecidable (x=y)
        exact slotFromPartitions d e he hL s F sign
          (fun g v r k => (genuineBase d (stepA (Nat.clog 2 size) 0) g v r k).divX) n
          (fun x => (genuineCross d (stepA (Nat.clog 2 size) 0) p₀ n.val he hL s x).divX) (stepA (Nat.clog 2 size) 0) p₀ f
          adr) := by
  simpa only [jointObservation_as_partitions] using
    (actual_singleton_eq_joint size C b f ell created d F sign mask wordsR wordsC
      hC hB ha hu huM rd cfg seed hf hF hℓ hCreated e he hL hr hc s off n hN idx)

#print axioms actual_singleton_eq_partitions
end
end P6Joint