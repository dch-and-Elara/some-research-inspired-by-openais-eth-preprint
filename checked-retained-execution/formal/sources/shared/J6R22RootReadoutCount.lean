
import J6R22RootReadoutNativeFactor
import J6R22RootReadoutOuter

/-! The integer-pair evaluator uses exactly the published odd mesh and
native signed old numerators. Equality with the original CNF count
does not ask for any unrelated rational table or correct-answer oracle. -/
namespace J6R22RootReadout
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval
open J6RepairedCentered J6NativeHeightMesh J6R15SignedRead J6R12Repack J6R14ZeroMode
open Std.Sat J7R10Plant J9R19CompiledBits J1PPrinted
set_option maxHeartbeats 16000000
set_option maxRecDepth 2000
set_option linter.unusedSectionVars false

theorem source_outer_exact
    {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {f : ℤ[X]} {ell : ℕ} [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (F : CNF V) (p l native : ℕ)
    (w : Fin (a (J7R10Readout.mCNF F))→Fin 64)
    (mask : MaskFamily (a (J7R10Readout.mCNF F)) (K (J7R10Readout.mCNF F)) (Fin 64))
    (hm : J7R10Readout.mCNF F≤K (J7R10Readout.mCNF F))
    (hL : 2*l=L (J7R10Readout.mCNF F)) (hn : native≤J7R10Readout.mCNF F)
    (hfield : f.natDegree=4*Nat.clog 2 (physicalSize (J7R10Readout.mCNF F) native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize (J7R10Readout.mCNF F) native))
    (hdeg : ∀ v,(physicalPlant (J7R10Readout.H F)).degree v≤sourceDelta (physicalSize (J7R10Readout.mCNF F) native))
    (hf : f.Monic) (hbase : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (menu : Prescribed f (literalDegree (J7R10Readout.mCNF F) native)) :
    let m := J7R10Readout.mCNF F
    let q := J7R10Readout.qCNF F
    let T := physicalPlant (J7R10Readout.H F)
    (outerAtOne m (sampleNum m) (sampleDen m) (rootOldNumerator m q T)).value-1=
      (PinnedCNF.modelCount F:ℚ) := by
  let m := J7R10Readout.mCNF F
  let q := J7R10Readout.qCNF F
  let T := physicalPlant (J7R10Readout.H F)
  let recv := printedNativeFallback (f:=f) (ell:=ell) p m l q native T w mask hm hL hn
    hfield hsize hdeg hf menu
  have fnum (i : J6Recovery.Addr m) :
      (receiverNumeral f ell m q p l mask w hm hL i hf hℓ (recv i)).1=rootOldNumerator m q T i := by
    refine congrArg Prod.fst (receiverNumeral_exact f ell m q p l T mask w hm hL i hf
      (printed_precision_pos m p) hF hℓ (recv i) (Fintype.card_fin 64) (planted_guard_zero F) ?_)
    exact (printedNativeFallback_eq_literal p m l q native T w mask hm hL hn hfield hsize hdeg hf
      hbase hF hℓ menu i).trans (finite_literalSlot f ell m q p l T mask w hm hL i)
  have fn : (fun i=> (sampleNum m i:ℚ)/sampleDen m i)=point m :=
    funext fun i=>(mesh_fraction m i).symm
  have h :=
    outer_at_one_exact m (sampleNum m) (sampleDen m) (rootOldNumerator m q T)
      (fun j=>(mesh_bounds m j).1.ne') (source_mesh_injective m)
  rw [fn] at h
  change (outerAtOne m (sampleNum m) (sampleDen m) (rootOldNumerator m q T)).value-1=_
  rw [h]
  have c := printedFallback_raw_count (f:=f) (ell:=ell) F p l native w mask hm hL hn
    hfield hsize hdeg hf hbase hF hℓ menu
  change (readLayer f ell m q p l mask w hm hL hf hℓ recv).eval 1-1=_ at c
  unfold readLayer at c
  have equal :
      (fun i => ((receiverNumeral f ell m q p l mask w hm hL i hf hℓ (recv i)).1:ℚ)/(sampleDen m i:ℚ)^m) =
      (fun i => ((rootOldNumerator m q T i):ℚ)/(sampleDen m i:ℚ)^m) := by
    funext i
    rw [fnum]
  rwa [equal] at c

#print axioms source_outer_exact
end J6R22RootReadout
