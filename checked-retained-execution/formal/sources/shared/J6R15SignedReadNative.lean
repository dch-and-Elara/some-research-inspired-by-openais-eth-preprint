import J6R15SignedReadRuntime
import J6R15SignedReadCleared
import J6R15PlantedIdentityRoot

/-! Final guard-preserving composition: actual outer beta=0 product,
raw signed J2 scalar, exactly centered receiver, signed integer odd
root and rational interpolation back to the original CNF count. -/
namespace J6R15SignedRead
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking P1DyadicGrid J6Mesh J6OrientedHost J6R9Recursive
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Integral J6R10Integral
open J6R12Repack J6R14ZeroMode J6R12Blueprint J6R11Blueprint J1PPrinted
open J6RepairedCentered J6NativeHeightResidue J6OrientedHostEval J6R11Repack
set_option maxHeartbeats 7800000


private theorem same_slot_instances {R P : Type*} [CommRing R]
    (F F' : Fintype P) (D D' : DecidableEq P)
    (A B : (P→Bool)→Bool) (read : P→(P→Bool)→Bool) (c : R) :
    @residueSlot R P _ F D A B read c =
      @residueSlot R P _ F' D' A B read c := by
  have hF : F=F' := Subsingleton.elim _ _
  have hD : D=D' := Subsingleton.elim _ _
  subst F'
  subst D'
  rfl
section Literal
variable {V : Type} [Fintype V] {f : ℤ[X]} {ell : ℕ}

theorem printedNativeZero_eq_literal
    (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree=4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v, T.degree v≤sourceDelta (physicalSize m native))
    (hf : f.Monic) (hbase : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (i : J6Recovery.Addr m) :
    printedNativeZero (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg hf i =
      J6ZeroTransport.reduceAt _ (box_two_nil (J6SourcePrecision.printed m p) f ell)
        (localLiteralSlot m q l T mask w hm hL i) := by
  let c := physicalRootCall f ell p m l q T w
  let Sₚ := rootParams f ell m native
  let t := oddRootCenter f ell p m l q native T w hn i
  let sel := exactJ6Selector (f:=f) (ell:=ell) p m l q native T w mask hm hL hn
  let d := exact_j6_root_ready (f:=f) (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg
  let hp := oddRootCenter_precision f ell p m l q native T w hn i
  let qₜ := registerPrecision Sₚ c t
  let ζ := J6R15PlantedIdentity.plantedScalar m l q T w mask hm hL i
  have h₀ := runtime_at_parent sel d t (exact_j6_root_bounds (f:=f) m native hfield hsize)
    (exact_j6_root_stable (f:=f) (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg) hf hF
  have h₁ := J6R15PlantedIdentity.selected_parent_at_odd p m l q native T w mask hm hL hn d
    i hf hbase hF hℓ
  have h₂ : zeroRuntime sel d t hf 0 =
      J6ZeroTransport.reduceAt qₜ (box_two_nil qₜ f ell) ζ := h₀.trans h₁
  have hζ : ζ = localLiteralSlot m q l T mask w hm hL i := by
    letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
    unfold localLiteralSlot
    refine (J6R15PlantedIdentity.plantedScalar_receives (RingHom.id DenominatorBudget.TwoLocal)
      m l q T w mask hm hL i).trans ?_
    exact same_slot_instances _ _ _ _ _ _ _ _
  change castBox f ell hp (zeroRuntime sel d t hf 0) = _
  rw [h₂,castBox_reduceAt,hζ]

theorem printedNativeFallback_eq_literal
    (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree=4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v, T.degree v≤sourceDelta (physicalSize m native))
    (hf : f.Monic) (hbase : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (menu : Prescribed f (literalDegree m native)) (i : J6Recovery.Addr m) :
    printedNativeFallback (ell:=ell) p m l q native T w mask hm hL hn
      hfield hsize hdeg hf menu i =
      J6ZeroTransport.reduceAt _ (box_two_nil (J6SourcePrecision.printed m p) f ell)
        (localLiteralSlot m q l T mask w hm hL i) := by
  exact (printedNativeFallback_eq_direct (ell:=ell) p m l q native T
    w mask hm hL hn hfield hsize hdeg hf hF menu i).trans
      (printedNativeZero_eq_literal p m l q native T w mask hm hL hn hfield hsize
        hdeg hf hbase hF hℓ i)


/-- Same signed validated intermediate, now on the actual selected fallback
table, before any public factor division or integer root. -/
theorem printedNativeFallback_cleared
    (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree=4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v, T.degree v≤sourceDelta (physicalSize m native))
    (hf : f.Monic) (hbase : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (menu : Prescribed f (literalDegree m native)) (i : J6Recovery.Addr m) :
    (((J6NativeHeightMesh.sampleDen m i : NativeProbeRing.Base (J6SourcePrecision.printed m p))^M m *
      boxProject (J6SourcePrecision.printed m p) f ell hf hℓ
        (printedNativeFallback p m l q native T w mask hm hL hn
          hfield hsize hdeg hf menu i)).valMinAbs) =
        physicalCleared m q l T mask w hm hL i := by
  refine receiverCleared_exact f ell m q p l T mask w hm hL i hf (printed_precision_pos m p)
    hF hℓ _ (Fintype.card_fin 64) ?_
  exact (printedNativeFallback_eq_literal p m l q native T w mask hm hL hn
    hfield hsize hdeg hf hbase hF hℓ menu i).trans
    (finite_literalSlot f ell m q p l T mask w hm hL i)
end Literal

open Std.Sat J7R10Plant
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ}
local notation "sz" => J7R10Readout.mCNF
local notation "cols" => J7R10Readout.qCNF
local notation "guarded" => J7R10Readout.H

theorem printedFallback_raw_count
    (F : CNF V) (p l native : ℕ)
    (w : Fin (a (sz F)) → Fin 64) (mask : MaskFamily (a (sz F)) (K (sz F)) (Fin 64))
    (hm : sz F≤K (sz F)) (hL : 2*l=L (sz F)) (hn : native≤sz F)
    (hfield : f.natDegree=4*Nat.clog 2 (physicalSize (sz F) native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize (sz F) native))
    (hdeg : ∀ v, (physicalPlant (guarded F)).degree v≤sourceDelta (physicalSize (sz F) native))
    (hf : f.Monic) (hbase : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (menu : Prescribed f (literalDegree (sz F) native)) :
    let recv := printedNativeFallback (ell:=ell) p (sz F) l (cols F) native
      (physicalPlant (guarded F)) w mask hm hL hn hfield hsize hdeg hf menu
    (readLayer f ell (sz F) (cols F) p l mask w hm hL hf hℓ recv).eval 1 - 1 =
      (PinnedCNF.modelCount F:ℚ) := by
  dsimp only
  refine readRaw_count f ell p l F mask w hm hL hf hF hℓ (Fintype.card_fin 64) _ (fun i => ?_)
  exact printedNativeFallback_eq_literal p (sz F) l (cols F) native
    (physicalPlant (guarded F)) w mask hm hL hn hfield hsize hdeg hf hbase hF hℓ menu i

#print axioms printedNativeZero_eq_literal
#print axioms printedNativeFallback_eq_literal
#print axioms printedNativeFallback_cleared
#print axioms printedFallback_raw_count
end J6R15SignedRead