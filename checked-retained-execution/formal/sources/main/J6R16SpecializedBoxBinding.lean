import J6R15SpecializedBoxFrame
import J6R16SpecializedBoxCrossChart
import J6R16SpecializedBoxTileType
import J6R16SpecializedBoxNormalize
import J6R16SpecializedBoxProjection
import J6R15SpecializedBoxOrientedSeat

/-! Exact J9 observation versus the product of the real weighted R12
children. The common tensor is the oriented seated equality/CNF source.
Packet and per-mode coefficients are not provided by an oracle. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral J6R10Integral
open J6R9PacketScopes J6R9PacketChild J6R9PacketCoeff J6R10RowIdentity
open J6R10RowLocal J6R10RowAffine J8Physical J8EndToEnd J8J9Grouped
open J9R15FrozenErasurePhysical J9R13PhysicalFusion J9R13PhysicalTables
open NativeProbeRing DyadicProbeCompiler LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false
local instance (priority := 10000) specializedBindingFinDecEq (n : ℕ) : DecidableEq (Fin n) :=
  fun j k => Classical.propDecidable (j=k)

variable {G R S V : Type} [LinearOrder G] {U : V→Type} {a b : ℕ}
variable (d : Layout (Page a b G) R S V G U (2^a))
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G]
variable [(v : V)→Fintype (U v)]
variable (mask : MaskFamily a b G)
variable (wordsR : R→Fin a→G) (wordsC : S⊕V→Fin a→G)
variable (hC : ∀ w : Wire R, physicalCell mask (d.seat w) =
  declaredCell (orientedNetwork d) wordsR wordsC w)
variable (hB : Nat.card (Cell (Fin a) G) * (b*2^a) ≤ 3*Nat.card (Wire R))

def seatedParentPacking : PhysicalPacking (orientedNetwork d) a G where
  rowLabel := wordsR
  colLabel := wordsC
  copies := b
  mask := mask
  seat := d.seat
  exactCell := hC
  paddedBudget := hB

local notation "Q" => (seatedParentPacking d mask wordsR wordsC hC hB)

theorem label_cube_eq {M : ℕ} (idx : Wire R ≃ Fin M) (X : Wire R→Bool) :
    (cubeEquiv d idx).symm (X ∘ idx.symm) = fun g => localLabels d g X := by
  apply (cubeEquiv d idx).injective
  rw [Equiv.apply_symm_apply]
  funext j
  exact (localLabels_cube d X (idx.symm j)).symm

set_option maxHeartbeats 2100000 in
theorem seated_actual_children_high_observation
    (i : Fin a) (hi : i.val=0)
    (hr : ∀ w, rowGroup mask i (d.seat w)=d.rowLabel w.1)
    (hc : ∀ w, colGroup mask i (d.seat w)=actualColLabel d w)
    (ht : ((2^a:ℕ):ℤ)-1≠0) (hv : padicValInt 2 (((2^a:ℕ):ℤ)-1)=i.val)
    (e : EndpointSeating d) (he : Even (2^a:ℕ)) (hL : 2<2^a)
    (p ell created : ℕ) (f : ℤ[X]) (hf : f.Monic) (hp : 0<p) (hCreated : 0<created) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (n : Fin (@Fintype.card (PinTile d s) (canonicalPinTile d s))) (hN : n.val<p-1)
    (F : OldTables d) (sign : S→Bool) {M : ℕ} (idx : Wire R ≃ Fin M)
    (adr : Fin f.natDegree→Bool) :
    let z := probe p f adr
    let m := anchoredMode d mask i hr hc s off (⟨n.val,hN⟩:Fin (p-1))
    actualProjection Q i ht hv p (J6ActiveInterpolation.scalarIn p f ell z)
      (orientedEntryFile d f ell created F sign) hf (Finsupp.single m 1) =
      J6ActiveInterpolation.scalarIn p f ell
        (by
          letI : DecidableEq G := fun x y => Classical.propDecidable (x=y)
          letI : DecidableEq (Page a b G) := fun x y => Classical.propDecidable (x=y)
          exact highObservation d e he hL s F sign
            (fun g v r k => (genuineBase d a g v r k).divX) n
            (fun j => (genuineCross d a p n.val he hL s j).divX) a p f adr) := by
  let z := probe p f adr
  let ξ := J6ActiveInterpolation.scalarIn p f ell z
  let m := anchoredMode d mask i hr hc s off (⟨n.val,hN⟩:Fin (p-1))
  let tails : IntegralArguments d := by
    letI : DecidableEq G := fun x y => Classical.propDecidable (x=y)
    letI : DecidableEq (Page a b G) := fun x y => Classical.propDecidable (x=y)
    exact fun g v r k => (genuineBase d a g v r k).divX
  let kt : TargetPorts d s→Source[X] := by
    letI : DecidableEq G := fun x y => Classical.propDecidable (x=y)
    letI : DecidableEq (Page a b G) := fun x y => Classical.propDecidable (x=y)
    exact fun j => (genuineCross d a p n.val he hL s j).divX
  let D := Box f ell p
  let scale : D := (2:D)^(a+1+n.val)*ξ
  let ψ := evalBox p f ell z
  let answerCompiled :=
    scale * ψ (MvPolynomial.coeff J9LayoutTransfer.β (completed
      (literalSystem d idx F sign) (literalBase d e he s idx tails n)
      (literalKernel d (M:=M) he hL s n kt)))
  have exactCompiled : actualProjection Q i ht hv p ξ (orientedEntryFile d f ell created F sign) hf
      (Finsupp.single m 1) = answerCompiled := by
    refine fixed_product_of_pointwise_entries Q i ht hv p ξ (orientedEntryFile d f ell created F sign) hf
      idx m ψ scale (globalCNF d idx F sign) (baseline d e he idx tails)
        (fun _ => crossing d he hL s n kt) (featureValue d s idx n) ?_ ?_ ?_ ?_ ?_
    · intro Y
      rw [oriented_rows_exact d f ell created F sign hf hCreated hF hℓ]
      exact map_truth (reduce p f ell) _ _
    · intro X
      rw [oriented_cols_exact d f ell created F sign hf hCreated hF hℓ X idx]
      exact map_truth (reduce p f ell) _ _
    · intro X w
      unfold baseline J9R13GroupFusion.baseAt
      rw [label_cube_eq d idx X]
      letI : DecidableEq G := fun x y => Classical.propDecidable (x=y)
      letI : DecidableEq (Page a b G) := fun x y => Classical.propDecidable (x=y)
      exact (genuine_samepage_box d mask i hr hc e he F p ell f (box_two_nil p f ell) z X w).symm
    · intro X w
      letI : DecidableEq G := fun x y => Classical.propDecidable (x=y)
      letI : DecidableEq (Page a b G) := fun x y => Classical.propDecidable (x=y)
      unfold crossing
      have H := actual_scaled_cross_by_decidability d mask i hr hc hi p ell hp f
        (box_two_nil p f ell) z he hL s off n.val hN ht hv w
      dsimp only at H
      exact H
    · intro X
      unfold featureValue
      rw [label_cube_eq d idx X]
      letI : DecidableEq (Page a b G) := Classical.decEq _
      exact actual_tile_moment_box d mask i hr hc hi p ell f z s off X n hN

  exact exactCompiled.trans (scalar_high_is_compiled d e he hL s off idx F sign tails n kt a p ell f adr).symm

#print axioms seatedParentPacking
#print axioms label_cube_eq
#print axioms seated_actual_children_high_observation
end
end J6R14SpecializedBox