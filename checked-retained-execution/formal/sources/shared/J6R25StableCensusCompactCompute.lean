
import J6R25StableCensusRuntime
import J6R25StableCensusCompact
import J6R24LegalLayoutMode

/-! From compact planted metadata and the new layout's completed U/V
slots to the final ordinary CNF count. The runtime prepares and reads
its own raw padding tape; neither per-column loads, denominator words
nor typed paired positions are extra inputs. -/
namespace J6R25StableCensus
open scoped Polynomial BigOperators Classical
open Polynomial Std.Sat P11FullPacking J6Mesh J6OrientedHost J6RecursiveOrientation
open J6R23PaddingCensus J6R24LegalLayout J6R14LayoutCost J6R9Recursive J6R22RootReadout
open J6R18ChildWrite J6R10Integral J6R11Repack J7R10Plant A1R10 A1R12 AOracleMachineTime
open J6NativeHeightMesh
set_option maxHeartbeats 6500000
set_option maxRecDepth 1500
set_option linter.unusedSectionVars false

def compactStableCount {P B R ell : ℕ} (hp : 0<P) (hb : 0<B) (hr : 0<R)
    {fw : List (Word P)} (m l q rankWidth : ℕ) (slots : J6Recovery.Addr m→UVBlock fw ell)
    (diag : CellWord) : Meter (Word R) :=
  let A := stablePadTape (a m) (K m) l rankWidth m diag
  let result := legalRootWords hp hb hr m q slots A.result
  ⟨result.result,A.steps+result.steps+8⟩

section Root
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {ell : ℕ}
local notation "pm" => J6SourcePrecision.printed

theorem compact_stable_native_words
    (m q base b l B R rankWidth : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (guard : J6OrientedHostEval.coreA T (fun _=>false)=true) (answer : ℕ)
    (outerValue : (outerAtOne m (sampleNum m) (sampleDen m) (rootOldNumerator m q T)).value-1=(answer:ℚ))
    (hm : m≤K m) (hL : 2*l=L m) (widthPos : 0<rankWidth)
    (rankA : a m≤rankWidth) (rankFit : K m*L m<2^rankWidth)
    (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (hp : 0<pm m b) (hb : 0<B) (hr : 0<R) {fw : List (Word (pm m b))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (pm m b) f)
    (slots : J6Recovery.Addr m→UVBlock fw ell)
    (received : ∀ i,
      J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (slots i)) =
       (J6R14ZeroMode.polynomial
        (stableRootPacking (V:=V) m l q rankWidth T w hm hL rankA rankFit.le)
        (oddAxis m) (index m i:ℤ) (pm m b)
        (rootEntryFile f ell base T w) hf).eval 0)
    (factorFit : publicFactorWidth m q (exactPadOrder m (K m) l w).length+2≤B)
    (outerFit : (baseTermWidth m (outerMeshWidth m) (pm m b)+1)*(m+1)+3≤R) :
    let n := (exactPadOrder m (K m) l w).length
    let out := compactStableCount hp hb hr m l q rankWidth slots (wordCell (diagonal w))
    bitsValue out.result.val=answer ∧
      out.steps≤stablePadBudget (a m) (K m) l rankWidth+
        legalRootBudget (pm m b) B R ell fw.length (rankWidth-a m+13*a m) m n+8 := by
  let C := deterministicLegal rankA rankFit.le w hm hL
  let A := stablePadTape (a m) (K m) l rankWidth m (wordCell (diagonal w))
  let order := exactPadOrder m (K m) l w
  obtain ⟨nd,all,cert,fee⟩ := stable_pad_tape_exact m l rankWidth widthPos rankA rankFit w hm hL
  have truth (i : J6Recovery.Addr m) :=
    (received i).trans (completed_stable_zero_expansion f ell base (pm m b)
      m l q rankWidth T w hm hL rankA rankFit.le hf hbase hp hF hℓ i)
  have codeFit := stable_page_width (a m) (K m) rankWidth rankA rankFit
  have Q := generic_legal_root_words m l q b B R (rankWidth-a m+13*a m) T w hm hL C
    guard answer outerValue f ell hf hF hℓ hp hb hr hPoly slots truth (pageCode (rankWidth-a m)) (page_code_injective _ codeFit)
    A.result order nd all cert factorFit outerFit
  refine ⟨Q.1,?_⟩
  change A.steps+(legalRootWords hp hb hr m q slots A.result).steps+8≤_
  exact Nat.add_le_add_right (Nat.add_le_add fee Q.2) _

end Root
#print axioms compact_stable_native_words
end J6R25StableCensus
