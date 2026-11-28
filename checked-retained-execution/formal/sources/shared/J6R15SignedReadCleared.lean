import J6R15SignedReadBase

/-! Explicit signed centered integer before public-factor division.
The numerator fit is derived for the actual repaired root width. -/
namespace J6R15SignedRead
open scoped Classical Polynomial BigOperators
open P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval J6RepairedCentered
open J6NativeHeight J6NativeHeightDyadic J6NativeHeightMesh J6NativeHeightResidue
open J6R9Recursive
set_option maxHeartbeats 2800000

variable {W S : Type*} [LinearOrder S] [Fintype S] [Fintype W]

noncomputable def physicalCleared
    (m q l : ℕ) (T : Plant W m q) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m) : ℤ := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  exact numerator (oldOK T w) (newOK T w)
    (fun k x => ((shiftAt m l mask w hm hL i k).map x).getD false)
    (sampleNum m i) (sampleDen m i)

theorem physicalCleared_fits
    (m q b l : ℕ) (T : Plant W m q) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m)
    (hS : Fintype.card S=64) :
    2*|physicalCleared m q l T mask w hm hL i| <
      (↑((2:ℕ)^J6SourcePrecision.printed m b) : ℤ) := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  let P := Ports m l w
  have hCard := J6RepairedCapacity.actual_wire_count m l w hm hL hS
  apply J6SourcePrecision.centered_fit_printed m b i
  unfold physicalCleared
  exact physical_height m (index m i) (P:=P) hCard (oldOK T w) (newOK T w)
    (fun k x => ((shiftAt m l mask w hm hL i k).map x).getD false)
    (sampleNum m i) (sampleDen m i) (mesh_bounds m i).2.1 (mesh_bounds m i).2.2

theorem receiverCleared_exact
    (f : Polynomial ℤ) (ell m q b l : ℕ) (T : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (hm : m≤K m) (hL : 2*l=L m) (i : J6Recovery.Addr m)
    (hf : f.Monic) (hp : 0<J6SourcePrecision.printed m b) (hF : 0<f.natDegree)
    (hℓ : 0<ell) (x : Box f ell (J6SourcePrecision.printed m b))
    (hS : Fintype.card S=64)
    (recv : x = boxBase _ f ell (literalRead m q b l T mask w hm hL i)) :
    (((sampleDen m i : NativeProbeRing.Base (J6SourcePrecision.printed m b))^M m *
      boxProject (J6SourcePrecision.printed m b) f ell hf hℓ x).valMinAbs) =
        physicalCleared m q l T mask w hm hL i := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  let p := J6SourcePrecision.printed m b
  let d := sampleDen m i
  let n := sampleNum m i
  let P := Ports m l w
  letI : NeZero ((2:ℕ)^p) := ⟨pow_ne_zero _ (by decide)⟩
  have hCard := J6RepairedCapacity.actual_wire_count m l w hm hL hS
  have hFit := physicalCleared_fits m q b l T mask w hm hL i hS
  rw [recv,boxProject_base _ _ _ _ hp hF]
  apply (ZMod.valMinAbs_spec _ _).mpr
  constructor
  · have h := residueClearing (P:=P) (oldOK T w) (newOK T w)
      (fun k x => ((shiftAt m l mask w hm hL i k).map x).getD false)
      n d ((J6ZeroTransport.reduceBase p) (scalar m i))
      (actual_scalar_clearing (J6ZeroTransport.reduceBase p) m i)
    rw [hCard] at h
    exact h.symm
  · change -(↑((2:ℕ)^p):ℤ) < physicalCleared m q l T mask w hm hL i*2 ∧
      physicalCleared m q l T mask w hm hL i*2 ≤ ↑((2:ℕ)^p)
    constructor <;> linarith [le_abs_self (physicalCleared m q l T mask w hm hL i),
      neg_le_abs (physicalCleared m q l T mask w hm hL i)]

#print axioms physicalCleared_fits
#print axioms receiverCleared_exact
end J6R15SignedRead