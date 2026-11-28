
import J6R26StablePreparedRootSite
import J6R26StablePreparedRootGather

/-! Metered outer execution on the stable root. No supplied raw slots:
they are produced from the requested Prepared subtrees by the actual
zero-mode probes, grouped products and unit interpolation, then the
same-layout R25 census and count program consume the materialized bank. -/
namespace J6R26StablePreparedRoot
open scoped Classical Polynomial BigOperators
open Polynomial J6R24LegalLayout J6Mesh J6R9Recursive J6OrientedHost
open Std.Sat J7R10Plant J6R22RootReadout J6R25StableCensus J6R18ChildWrite
open A1R10 AOracleMachineTime J6R24MeteredRecursion J6R22Active
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 2200

section CNF
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ} [Fact (Irreducible (NativeProbeRing.residuePoly f))]
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

theorem prepared_stable_cnf_count
    (F : CNF V) (base l native width B R : ℕ) (w : Fin (a (ms F))→Fin 64)
    (G : RootShape f (ms F) l base native width (physicalPlant (inp F)) w)
    (widthPos : 0<width) (frame : Frame f (pm (ms F) base))
    (hf : f.Monic) (hbase : 0<base) (hv : 0<ell) (hb : 0<B) (hr : 0<R)
    (source : ∀ i,LiteralSite (ell:=ell) G frame hf i)
    (factorFit : publicFactorWidth (ms F) (qs F) (exactPadOrder (ms F) (K (ms F)) l w).length+2≤B)
    (outerFit : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) base)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let n := (exactPadOrder m (K m) l w).length
    let sites := fun i=>literalSlot G frame hf hv i (source i)
    let out := countFromMeasuredSlots frame hb hr m l (qs F) width
      (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w)) sites
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps≤stablePadBudget (a m) (K m) l width+
        legalRootBudget (pm m base) B R ell frame.words.length (width-a m+13*a m) m n+8+
        gatherCost frame m sites := by
  let m := ms F
  let q := qs F
  let sites (i : J6Recovery.Addr m) := literalSlot G frame hf hv i (source i)
  let slots (i : J6Recovery.Addr m) := (slotRead frame m sites i).result
  have hF : 0<f.natDegree := frame.natDegree hf ▸ frame.sizePos
  have word (i : J6Recovery.Addr m) :
      frame.decode (slots i)=
        (J6R14ZeroMode.polynomial
          (stableRootPacking m l q width (physicalPlant (inp F)) w G.room G.half G.rankA G.rankFit.le)
          (oddAxis m) (index m i:ℤ) (pm m base) (J6R11Repack.rootEntryFile f ell base (physicalPlant (inp F)) w) hf).eval 0 := by
    change frame.decode (slotRead frame m sites i).result=_
    rw [(stored_slot_exact frame m sites i).1]
    exact literal_slot_exact G frame hf hv i (source i)
  have Q := compact_stable_raw_count F base base l B R width w G.room G.half widthPos
    G.rankA G.rankFit hf hbase hF hv frame.hp hb hr frame.exactMod slots
    (fun i=>by
      have h := word i
      change boxTransport frame.exactMod (uvRead frame.hp frame.words ell (slots i))=_ at h
      simpa only [boxTransport_cast] using h) factorFit outerFit
  have D := metered_slot_append frame hb hr m l q width
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w)) sites
  refine ⟨?_,D.2.trans (Nat.add_le_add_right Q.2 _)⟩
  exact (congrArg (fun x : Word R=>bitsValue x.val) D.1).trans Q.1

end CNF
#print axioms prepared_stable_cnf_count
end J6R26StablePreparedRoot
