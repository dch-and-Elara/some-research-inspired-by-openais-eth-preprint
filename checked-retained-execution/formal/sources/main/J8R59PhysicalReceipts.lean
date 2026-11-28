import J8R59SourceChildren
import J6R16SpecializedBoxBinding
import J6R16SpecializedBoxRoot

/-! The anchored singleton is fixed for all prescribed binary words, on the same selected packet seats, old truth tables and extreme positive center. Each sample is a product of the actual 64 recursive child calls. -/
namespace J8R59
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes J6R9PacketChild
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral J1PPrinted
open NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler
open J6R14SpecializedBox J9R15FrozenErasurePhysical
noncomputable section
set_option linter.unusedSectionVars false

variable {R S V : Type} {U : V→Type} 
variable [Fintype R] [Fintype S] [Fintype V] [(v:V)→Fintype (U v)]
set_option maxHeartbeats 4000000 in
theorem literal_same_center_anchored_singleton
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
        exact highObservation d e he hL s F sign
          (fun g v r k => (genuineBase d (stepA (Nat.clog 2 size) 0) g v r k).divX) n
          (fun x => (genuineCross d (stepA (Nat.clog 2 size) 0) p₀ n.val he hL s x).divX) (stepA (Nat.clog 2 size) 0) p₀ f
          adr) := by
  dsimp only
  let t₀ := extremeCenter (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) ha hu huM
  let p₀ := registerPrecision (printedParams (f:=f) (ell:=ell) size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) t₀
  let i₀ := centerIndex (S:=(printedParams (f:=f) (ell:=ell) size)) (Δ:=sourceDelta size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) rd t₀
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
  let ans (adr : Fin f.natDegree → Bool) := J6ActiveInterpolation.scalarIn p₀ f ell (by
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
      ∀ adr : Fin f.natDegree → Bool,
        actualProjection Q i₀ ht hv p₀ (wordNode (size:=size) t₀ adr)
          (orientedEntryFile d f ell created F sign) hf β.val = ans adr := by
    intro Q hQ
    subst Q
    let q := (⟨n.val,hN⟩ : Fin (p₀-1))
    let m := anchoredMode d mask i₀ hr' hc' s off q
    have hLegal := anchored_singleton_legal d mask i₀ hr' hc' s off q
    refine ⟨⟨Finsupp.single m 1,hLegal⟩,by rw [Finsupp.support_single_ne_zero m (one_ne_zero : (1:ℕ)≠0),Finset.card_singleton],?_⟩
    intro adr
    exact seated_actual_children_high_observation d mask wordsR wordsC hC hB i₀ hi hr' hc' ht hv
      e he hL p₀ ell created f hf hp hCreated hF hℓ s off n hN F sign idx adr
  obtain ⟨β,hOne,hObs⟩ := exactEntry P' eP
  refine ⟨β,hOne,?_⟩
  intro adr
  exact (word_completed_is_actual_projection (size:=size) (c:=(J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created)) (exactSeatSelector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) (J6ActiveRun.Call.mk (physicalHost (orientedNetwork d) (orientedEntryFile d f ell created F sign)) 0 (Fintype.card (Wire R)) created) (seatedParentPacking d mask wordsR wordsC hC hB)) rd t₀ adr β cfg seed hf hF).trans (hObs adr)

#print axioms literal_same_center_anchored_singleton
end
end J8R59