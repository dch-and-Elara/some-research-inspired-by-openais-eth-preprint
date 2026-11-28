
import J6R25StableCensusCompactCompute

/-! From compact planted metadata and the new layout's completed U/V
slots to the final ordinary CNF count. The runtime prepares and reads
its own raw padding tape; neither per-column loads, denominator words
nor typed paired positions are extra inputs. -/
namespace J6R25StableCensus
open scoped Polynomial BigOperators Classical
open Polynomial Std.Sat P11FullPacking J6Mesh J6OrientedHost J6RecursiveOrientation
open J6R23PaddingCensus J6R24LegalLayout J6R14LayoutCost J6R9Recursive J6R22RootReadout
open J6R18ChildWrite J6R10Integral J6R11Repack J7R10Plant A1R10 A1R12 AOracleMachineTime
set_option maxHeartbeats 6500000
set_option maxRecDepth 1500
set_option linter.unusedSectionVars false

section Root
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

theorem compact_stable_raw_count
    (F : CNF V) (base b l B R rankWidth : ℕ) (w : Fin (a (ms F))→Fin 64)
    (hm : ms F≤K (ms F)) (hL : 2*l=L (ms F)) (widthPos : 0<rankWidth)
    (rankA : a (ms F)≤rankWidth) (rankFit : K (ms F)*L (ms F)<2^rankWidth)
    (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (hp : 0<pm (ms F) b) (hb : 0<B) (hr : 0<R) {fw : List (Word (pm (ms F) b))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (pm (ms F) b) f)
    (slots : J6Recovery.Addr (ms F)→UVBlock fw ell)
    (received : ∀ i,
      J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (slots i)) =
       (J6R14ZeroMode.polynomial
        (stableRootPacking (ms F) l (qs F) rankWidth (physicalPlant (inp F)) w hm hL rankA rankFit.le)
        (oddAxis (ms F)) (index (ms F) i:ℤ) (pm (ms F) b)
        (rootEntryFile f ell base (physicalPlant (inp F)) w) hf).eval 0)
    (factorFit : publicFactorWidth (ms F) (qs F) (exactPadOrder (ms F) (K (ms F)) l w).length+2≤B)
    (outerFit : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) b)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let n := (exactPadOrder m (K m) l w).length
    let out := compactStableCount hp hb hr m l (qs F) rankWidth slots (wordCell (diagonal w))
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
    out.steps≤stablePadBudget (a m) (K m) l rankWidth+
        legalRootBudget (pm m b) B R ell fw.length (rankWidth-a m+13*a m) m n+8 := by
  exact compact_stable_native_words (ms F) (qs F) base b l B R rankWidth (physicalPlant (inp F)) w
    (planted_guard_zero F) (PinnedCNF.modelCount F) (exact_plain_outer_count F)
    hm hL widthPos rankA rankFit hf hbase hF hℓ hp hb hr hPoly slots received factorFit outerFit

end Root
#print axioms compact_stable_raw_count
end J6R25StableCensus
