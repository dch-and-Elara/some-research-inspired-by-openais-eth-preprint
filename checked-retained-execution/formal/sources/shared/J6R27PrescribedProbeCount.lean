
import J6R27PrescribedProbeRoot
import J6R26StablePreparedRootCount

/-! The original external probe words are produced once for the full
root. This wrapper removes the separate reader input to R26 while
retaining the exact typed Prepared-subtree assumptions. -/
namespace J6R27PrescribedProbe
open scoped Polynomial Classical BigOperators
open Polynomial A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J7R10Plant Std.Sat
open J6R26StablePreparedRoot J6R24MeteredRecursion J6R25StableCensus J6R22RootReadout
set_option maxHeartbeats 13000000
set_option maxRecDepth 2000
set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

noncomputable def countFromGeneratedProbes
    (F : CNF V) (base l native width B R : ℕ) (w : Fin (a (ms F))→Fin 64)
    (G : RootShape f (ms F) l base native width (physicalPlant (inp F)) w)
    (frame : Frame f (pm (ms F) base)) (hf : f.Monic) (hv : 0<ell) (hb : 0<B) (hr : 0<R)
    (subtrees : ∀ i,GeneratedChildren (ell:=ell) G hf i) : Meter (Word R) :=
  let A := buildRootBitBank G ell
  let I := fun i=>bindLiteralInput (ell:=ell) G frame hf i A.result (subtrees i)
  let sites := fun i=>literalSlot (ell:=ell) G frame hf hv i (I i)
  let count := countFromMeasuredSlots frame hb hr (ms F) l (qs F) width
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w)) sites
  ⟨count.result,count.steps+A.steps+4⟩

theorem generated_prescribed_cnf_count [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (F : CNF V) (base l native width B R : ℕ) (w : Fin (a (ms F))→Fin 64)
    (G : RootShape f (ms F) l base native width (physicalPlant (inp F)) w)
    (widthPos : 0<width) (frame : Frame f (pm (ms F) base))
    (hf : f.Monic) (hbase : 0<base) (hv : 0<ell) (hb : 0<B) (hr : 0<R)
    (subtrees : ∀ i,GeneratedChildren (ell:=ell) G hf i)
    (factorFit : publicFactorWidth (ms F) (qs F) (exactPadOrder (ms F) (K (ms F)) l w).length+2≤B)
    (outerFit : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) base)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let d := externalProbeDegree (J6Mesh.physicalSize m native)
      (J6R11Repack.physicalRootCall f ell base m l (qs F) (physicalPlant (inp F)) w)
    let n := (exactPadOrder m (K m) l w).length
    let A := buildRootBitBank G ell
    let I := fun i=>bindLiteralInput (ell:=ell) G frame hf i A.result (subtrees i)
    let sites := fun i=>literalSlot (ell:=ell) G frame hf hv i (I i)
    let out := countFromGeneratedProbes F base l native width B R w G frame hf hv hb hr subtrees
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps≤stablePadBudget (a m) (K m) l width+
        legalRootBudget (pm m base) B R ell frame.words.length (width-a m+13*a m) m n+8+
        gatherCost frame m sites+(positiveTapeFee f.natDegree (d+1)+3)+4 := by
  let m := ms F
  let d := externalProbeDegree (J6Mesh.physicalSize m native)
    (J6R11Repack.physicalRootCall f ell base m l (qs F) (physicalPlant (inp F)) w)
  let A := buildRootBitBank G ell
  let I := fun i=>bindLiteralInput (ell:=ell) G frame hf i A.result (subtrees i)
  let sites := fun i=>literalSlot (ell:=ell) G frame hf hv i (I i)
  let count := countFromMeasuredSlots frame hb hr m l (qs F) width
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w)) sites
  have C := prepared_stable_cnf_count F base l native width B R w G widthPos frame
    hf hbase hv hb hr I factorFit outerFit
  have fee : A.steps=positiveTapeFee f.natDegree (d+1)+3 := (build_root_probe_receipt G ell).1
  refine ⟨C.1,?_⟩
  change count.steps+A.steps+4≤_
  rw [fee]
  exact Nat.add_le_add_right (Nat.add_le_add_right C.2 _) _

#print axioms generated_prescribed_cnf_count
end J6R27PrescribedProbe
