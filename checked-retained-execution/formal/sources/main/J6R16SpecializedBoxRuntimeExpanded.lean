import J6R16SpecializedBoxBinding
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
open J9R15FrozenErasurePhysical
noncomputable section
set_option linter.unusedSectionVars false

variable {R S V : Type} {U : V→Type} 
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
set_option maxHeartbeats 4000000 in
theorem literal_oriented_same_recursive_register
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
    {M : ℕ} (idx : Wire R≃Fin M) (probeIndex : Probe (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) :
    let t₀ := extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM
    let p₀ := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) t₀
    ∃ β : LiteralMenu (exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (seatedParentPacking d mask wordsR wordsC hC hB)) rd t₀, β.val.support.card=1 ∧
      printedPacketProduct (s:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) (exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (seatedParentPacking d mask wordsR wordsC hC hB)) rd t₀ probeIndex β hf =
      J6ActiveInterpolation.scalarIn p₀ f ell (by
        letI : DecidableEq (Fin 64) := fun x y => Classical.propDecidable (x=y)
        letI : DecidableEq (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := fun x y => Classical.propDecidable (x=y)
        exact highObservation d e he hL s F sign
          (fun g v r k => (genuineBase d (stepA (Nat.clog 2 size) 0) g v r k).divX) n
          (fun x => (genuineCross d (stepA (Nat.clog 2 size) 0) p₀ n.val he hL s x).divX) (stepA (Nat.clog 2 size) 0) p₀ f
          (chosenRep f.natDegree _ rd.fit probeIndex)) := by
  dsimp only
  let t₀ := extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM
  let p₀ := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) t₀
  let i₀ := centerIndex (S:=(printedParams (f:=f) (ell:=ell) size)) (Δ:=sourceDelta size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) rd t₀
  let adr := chosenRep f.natDegree _ rd.fit probeIndex
  have hi : (i₀).val=0 := extremeCenter_index (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) rd ha hu huM
  let iFixed : Fin (stepA (Nat.clog 2 size) 0) := i₀
  have hIdx : iFixed = Fin.mk 0 ha := Fin.ext hi
  have hr' : ∀ w : Wire R, rowGroup mask iFixed (d.seat w)=d.rowLabel w.1 := by
    simpa only [hIdx] using hr
  have hc' : ∀ w : Wire R, colGroup mask iFixed (d.seat w)=actualColLabel d w := by
    simpa only [hIdx] using hc
  have hp := register_positive rd t₀
  have hCenter : t₀.val = Int.ofNat ((2:ℕ)^(stepA (Nat.clog 2 size) 0))-1 := rfl
  have ht : Int.ofNat ((2:ℕ)^(stepA (Nat.clog 2 size) 0))-1≠0 := by
    rw [← hCenter]
    exact centerNonzero t₀
  have hv : padicValInt 2 (Int.ofNat ((2:ℕ)^(stepA (Nat.clog 2 size) 0))-1)=i₀.val := by
    rw [← hCenter]
    rfl
  let ans := J6ActiveInterpolation.scalarIn p₀ f ell (by
    letI : DecidableEq (Fin 64) := fun x y => Classical.propDecidable (x=y)
    letI : DecidableEq (Page (stepA (Nat.clog 2 size) 0) b (Fin 64)) := fun x y => Classical.propDecidable (x=y)
    exact highObservation d e he hL s F sign
      (fun g v r k => (genuineBase d (stepA (Nat.clog 2 size) 0) g v r k).divX) n
      (fun x => (genuineCross d (stepA (Nat.clog 2 size) 0) p₀ n.val he hL s x).divX) (stepA (Nat.clog 2 size) 0) p₀ f adr)
  let P' := packing (exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (seatedParentPacking d mask wordsR wordsC hC hB)) rd
  have eP : P' = (seatedParentPacking d mask wordsR wordsC hC hB) := exactSeatSelector_at_root (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (seatedParentPacking d mask wordsR wordsC hC hB) rd
  have exactEntry :
      ∀ Q : PhysicalPacking (orientedNetwork d) (stepA (Nat.clog 2 size) 0) (Fin 64), Q=(seatedParentPacking d mask wordsR wordsC hC hB) →
      ∃ β : {η : Mode i₀ p₀ Q.mask→₀ℕ // η ∈
        J6RecursiveMenu.menu p₀ (J6R10RowAffine.weight i₀ p₀ Q.mask)},
        β.val.support.card=1 ∧
        actualProjection Q i₀ ht hv p₀ (sampleNode (printedParams (f:=f) (ell:=ell) size) f ell (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) rd.fit t₀ probeIndex)
          (orientedEntryFile d f ell created F sign) hf β.val = ans := by
    intro Q hQ
    subst Q
    let q := (⟨n.val,hN⟩ : Fin (p₀-1))
    let m := anchoredMode d mask i₀ hr' hc' s off q
    have hLegal := anchored_singleton_legal d mask i₀ hr' hc' s off q
    refine ⟨⟨Finsupp.single m 1,hLegal⟩,by rw [Finsupp.support_single_ne_zero m (one_ne_zero : (1:ℕ)≠0),Finset.card_singleton],?_⟩
    rw [literal_address_at_sample (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) rd t₀ probeIndex]
    exact seated_actual_children_high_observation d mask wordsR wordsC hC hB i₀ hi hr' hc' ht hv
      e he hL p₀ ell created f hf hp hCreated hF hℓ s off n hN F sign idx adr
  obtain ⟨β,hOne,hObs⟩ := exactEntry P' eP
  exact ⟨β,hOne,(printedPacketProduct_exact (s:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) (exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (seatedParentPacking d mask wordsR wordsC hC hB)) rd t₀ probeIndex β hf cfg seed hF).trans hObs⟩

#print axioms literal_oriented_same_recursive_register
end
end J6R14SpecializedBox