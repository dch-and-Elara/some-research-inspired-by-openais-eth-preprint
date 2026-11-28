
import J6R26StablePreparedRootGeometry
import J6R26StablePreparedRootInput
import J6R26StablePreparedRootFrame
import J6R12RepackRootStable

/-! Bind all the dependent odd-register frames to the same physical
root and stable selector. Each addressed zero-mode child is a precisely
typed Prepared input, not raw data from an earlier layout. -/
namespace J6R26StablePreparedRoot
open scoped Polynomial Classical
open Polynomial J6Mesh J6OrientedHost J6R9Recursive
open J6R10Integral J6R11Repack J6R11Blueprint J6R12Blueprint J6R12Repack J1PPrinted
open J6R24LegalLayout J6ActiveRun J6ActiveSchedule J6R14ZeroMode J6R24MeteredRecursion
open A1R10 AOracleMachineTime
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000
set_option maxRecDepth 1800

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {ell m l q b native width : ℕ}
variable {T : Plant V m q} {w : Fin (a m)→Fin 64}

structure RootShape (f : ℤ[X]) (m l b native width : ℕ) (T : Plant V m q)
    (w : Fin (a m)→Fin 64) : Prop where
  room : m≤K m
  half : 2*l=L m
  nativeFits : native≤m
  rankA : a m≤width
  rankFit : K m*L m<2^width
  fieldDegree : f.natDegree=4*Nat.clog 2 (physicalSize m native)
  size : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m native)
  degree : ∀ v,T.degree v≤sourceDelta (physicalSize m native)

variable (G : RootShape f m l b native width T w)

noncomputable abbrev RootShape.selector (ell : ℕ) :=
  stableSelector (f:=f) (ell:=ell) b m l q native width T w
    G.room G.half G.nativeFits G.rankA G.rankFit.le

abbrev RootShape.ready (ell : ℕ) :=
  exact_j6_root_ready (f:=f) (ell:=ell) b m l q native T w (fun _ _ _=>false)
    G.room G.half G.nativeFits G.fieldDegree G.size G.degree

abbrev RootShape.stable (ell : ℕ) :=
  exact_j6_root_stable (f:=f) (ell:=ell) b m l q native T w (fun _ _ _=>false)
    G.room G.half G.nativeFits G.fieldDegree G.size G.degree

abbrev RootShape.bounds :=
  exact_j6_root_bounds (f:=f) m native G.fieldDegree G.size

abbrev RootShape.centre (ell : ℕ) (i : J6Recovery.Addr m) :=
  oddRootCenter f ell b m l q native T w G.nativeFits i

abbrev RootShape.precision (ell : ℕ) (i : J6Recovery.Addr m) :=
  oddRootCenter_precision f ell b m l q native T w G.nativeFits i

local notation "P" => J6SourcePrecision.printed m b


noncomputable abbrev LiteralSite (F : Frame f P) (hf : f.Monic) (i : J6Recovery.Addr m) :=
  @FixedProbeInput f ell (physicalSize m native) 2 G.bounds (G.selector ell)
    (physicalRootCall f ell b m l q T w) hf (G.ready ell) (G.centre ell i)
    (siteFrame (G.precision ell i) F)

noncomputable def literalJob
    (F : Frame f P) (hf : f.Monic)
    (i : J6Recovery.Addr m) (I : LiteralSite (ell:=ell) G F hf i) :
    ProbeJob f ell (physicalSize m native) 2 G.bounds (G.selector ell)
      (physicalRootCall f ell b m l q T w) hf :=
  I.toJob

noncomputable def literalSlot
    (F : Frame f P) (hf : f.Monic) (hv : 0<ell)
    (i : J6Recovery.Addr m) (I : LiteralSite (ell:=ell) G F hf i) :
    Meter (Block F ell) :=
  let J := literalJob (ell:=ell) G F hf i I
  restoreFrame (G.precision ell i) F (J.completedWords hv I.2.1.read)

theorem literal_slot_exact (F : Frame f P) (hf : f.Monic) (hv : 0<ell)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (i : J6Recovery.Addr m) (I : LiteralSite (ell:=ell) G F hf i) :
    F.decode (literalSlot (ell:=ell) G F hf hv i I).result=
      (polynomial (stableRootPacking m l q width T w G.room G.half G.rankA G.rankFit.le)
        (oddAxis m) (index m i:ℤ) P (rootEntryFile f ell b T w) hf).eval 0 := by
  let J := literalJob (ell:=ell) G F hf i I
  let Q := J.completedWords hv I.2.1.read
  let out := restoreFrame (G.precision ell i) F Q
  have h := (J.completed_exact hv (G.stable ell) I.2.1.read I.2.1.consistent).1
  have h' : (siteFrame (G.precision ell i) F).decode Q.result =
      (physicalZeroP (G.selector ell) (G.ready ell) (G.centre ell i) hf).eval 0 := h
  change F.decode out.result=_
  rw [(restore_frame_receipt (G.precision ell i) F Q).1,h']
  exact physical_zero_is_stable b m l q native width T w G.room G.half G.nativeFits
    G.rankA G.rankFit.le (G.ready ell) hf i

#print axioms literal_slot_exact
end J6R26StablePreparedRoot
