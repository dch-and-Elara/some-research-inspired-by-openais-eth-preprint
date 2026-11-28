import J6R16SpecializedBoxRuntimeExpanded
import J6R16SpecializedBoxReadReceipt
import J6R16SpecializedBoxRunProduct
import J6R16SpecializedBoxRoot

/-! Execute precisely the same legal nonzero singleton as the J9
observation, with original parent creation tags and printed register
precision, via the actual D recursion. Its complete register remains
a product of real returned children, not a free group-value query. -/
namespace J6R14SpecializedBox
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J9R15FrozenErasurePhysical J9R13PhysicalTables LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false

variable {R S V : Type} {U : V→Type} 
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
set_option maxHeartbeats 4000000 in
theorem literal_recursive_receipts_signed_first
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
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (n : Fin (@Fintype.card (PinTile d s) (canonicalPinTile d s))) (hN : n.val<registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM)-1)
    {M : ℕ} (idx : Wire R≃Fin M)
    (hCube : ((2:ℕ)^(stepA (Nat.clog 2 size) 0))^3≤M) (capacity : ((2:ℕ)^(stepA (Nat.clog 2 size) 0))*Fintype.card (Page (stepA (Nat.clog 2 size) 0) b (Fin 64))≤3*M)
    (rows : (Fin M→Bool)→R→Bool→ℚ[X]) (cross : Fin ((2:ℕ)^(stepA (Nat.clog 2 size) 0))→ℚ[X]) (source : (Fin M→Bool)→ℚ[X])
    (hP : 10*M≤registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM))
    (hMenu : 10*M+1≤J9PrintedSchedule.probeCount (Fintype.card (Wire R)) ((2:ℕ)^(stepA (Nat.clog 2 size) 0))) :
    let ctr := (extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM)
    let prec := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ctr
    let sel := exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size)
      (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (seatedParentPacking d mask wordsR wordsC hC hB)
    ∃ choices : Fin (10*M+1)→LiteralMenu sel rd ctr,
      (∀ i, (choices i).val.support.card=1) ∧
      let fit := hMenu.trans rd.fit
      let chart : J9FactorBounds.Chart ((2:ℕ)^(stepA (Nat.clog 2 size) 0)) M R (J9End.Tile d s) := by
        let pageFinite : Fintype (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := inferInstance
        letI : DecidableEq (Fin 64) := fun x y => Classical.propDecidable (x=y)
        letI : Fintype (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := pageFinite
        letI : DecidableEq (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := fun x y => Classical.propDecidable (x=y)
        exact J9End.chart d s idx (satisfied (globalCNF d idx F sign))
      let x := fun i => probe (10*M) f (chosenRep f.natDegree (10*M+1) fit i)
      let recv : Fin (10*M+1)→Box f ell prec := fun i =>
        printedPacketProduct (s:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) sel rd ctr (Fin.castLE hMenu i) (choices i) hf
      let y := fun i => reduceScalar (10*M) prec hP f (atZero prec f ell hℓ (recv i))
      ((projectBase (10*M) f hf ((J9FactorBounds.publicDenominator chart n : Scalar (10*M) f) *
        NativeInterpolation.decode x y ⟨1,by
          have hM : 0<M := (show 0<((2:ℕ)^(stepA (Nat.clog 2 size) 0))^3 by positivity).trans_le hCube
          omega⟩)).valMinAbs:ℚ) / J9FactorBounds.publicDenominator chart n =
      (J9End.literalCompleted chart n rows cross source).coeff 1 := by
  dsimp only
  let ctr := (extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM)
  let prec := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ctr
  have hSample (i : Fin (10*M+1)) :=
    literal_oriented_same_recursive_register size C b f ell created d F sign mask wordsR wordsC hC hB
      ha hu huM rd cfg seed hf hF hℓ hCreated e he (show 2<((2:ℕ)^(stepA (Nat.clog 2 size) 0)) by omega) hr hc s off n hN idx (Fin.castLE hMenu i)
  choose β hβ hObs using hSample
  refine ⟨β,hβ,?_⟩
  let selExact := exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (seatedParentPacking d mask wordsR wordsC hC hB)
  let recv (i : Fin (10*M+1)) : Box f ell prec :=
    printedPacketProduct (s:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) selExact rd ctr (Fin.castLE hMenu i) (β i) hf
  let pageFinite : Fintype (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := inferInstance
  letI : DecidableEq (Fin 64) := fun x y => Classical.propDecidable (x=y)
  letI : Fintype (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := pageFinite
  letI : DecidableEq (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := fun x y => Classical.propDecidable (x=y)
  refine signed_first_from_verified_receipts d e he hL (stepA (Nat.clog 2 size) 0) rfl s off idx hCube capacity
    F sign (fun g v r k => (genuineBase d (stepA (Nat.clog 2 size) 0) g v r k).divX) n
    (fun x => (genuineCross d (stepA (Nat.clog 2 size) 0) prec n.val he (by omega) s x).divX)
    rows cross source prec ell hP hℓ f hf hF (hMenu.trans rd.fit) recv ?_
  intro i
  simpa only [recv,selExact,printed_probe_prefix f.natDegree _ (10*M+1) hMenu rd.fit (hMenu.trans rd.fit) i] using hObs i

#print axioms literal_recursive_receipts_signed_first
end
end J6R14SpecializedBox