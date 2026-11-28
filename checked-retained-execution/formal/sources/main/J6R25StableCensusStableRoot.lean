
import J6R25StableCensusRoot
import J6R24LegalLayoutMode

/-! The same-chart final statement. The acquired U/V slot is compared
to the *actual completed zero-mode polynomial on the new stable
packing*, and its own padding positions supply the factor rather than
any normalized comparison with the former layout. -/
namespace J6R25StableCensus
open scoped Polynomial BigOperators Classical
open Polynomial Std.Sat P11FullPacking J6Mesh J6OrientedHost J6R23PaddingCensus
open J6R24LegalLayout J6R9Recursive J6R22RootReadout J6R18ChildWrite
open J6R10Integral J6R11Repack J7R10Plant A1R10 A1R12 AOracleMachineTime
set_option maxHeartbeats 28000000
set_option maxRecDepth 2500
set_option linter.unusedSectionVars false

def stableCountWords {P B R ell : ℕ} (hp : 0<P) (hb : 0<B) (hr : 0<R)
    {fw : List (Word P)} (m q width : ℕ) (slots : J6Recovery.Addr m→UVBlock fw ell)
    (positions : List (PositionedPad (a m) (K m))) : Meter (Word R) :=
  let prep := exportActualLayout width positions
  let result := legalRootWords hp hb hr m q slots prep.result
  ⟨result.result,prep.steps+result.steps+8⟩

section Root
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

theorem stable_completed_count_words
    (F : CNF V) (base b l B R rankWidth pageWidth : ℕ) (w : Fin (a (ms F))→Fin 64)
    (hm : ms F≤K (ms F)) (hL : 2*l=L (ms F))
    (rankA : a (ms F)≤rankWidth) (rankFit : K (ms F)*L (ms F)≤2^rankWidth)
    (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (hp : 0<pm (ms F) b) (hb : 0<B) (hr : 0<R) {fw : List (Word (pm (ms F) b))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (pm (ms F) b) f)
    (slots : J6Recovery.Addr (ms F)→UVBlock fw ell)
    (received : ∀ i,
      J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (slots i)) =
       (J6R14ZeroMode.polynomial
        (stableRootPacking (ms F) l (qs F) rankWidth (physicalPlant (inp F)) w hm hL rankA rankFit)
        (oddAxis (ms F)) (index (ms F) i:ℤ) (pm (ms F) b)
        (rootEntryFile f ell base (physicalPlant (inp F)) w) hf).eval 0)
    (positions : List (PositionedPad (a (ms F)) (K (ms F))))
    (order : List (NativePad (ms F) l w)) (nd : order.Nodup) (all : order.toFinset=Finset.univ)
    (trueSeats : legallyPositioned (ms F) l w hm hL (deterministicLegal rankA rankFit w hm hL) positions order)
    (pageFit : K (ms F)≤2^pageWidth)
    (factorFit : publicFactorWidth (ms F) (qs F) order.length+2≤B)
    (outerFit : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) b)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let out := stableCountWords hp hb hr m (qs F) pageWidth slots positions
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps≤4+order.length*exportFee (a m) pageWidth+
        legalRootBudget (pm m b) B R ell fw.length (pageWidth+13*a m) m order.length+8 := by
  let m := ms F
  let q := qs F
  let C := deterministicLegal rankA rankFit w hm hL
  let raw := exportActualLayout pageWidth positions
  obtain ⟨cert,fee⟩ := export_legal_positions m l pageWidth w hm hL C positions order trueSeats
  have truth (i : J6Recovery.Addr m) :=
    (received i).trans (completed_stable_zero_expansion f ell base (pm m b)
      m l q rankWidth (physicalPlant (inp F)) w hm hL rankA rankFit hf hbase hp hF hℓ i)
  have A := exact_count_from_one_legal_chart F b l B R (pageWidth+13*a m) w hm hL C hf hF hℓ
    hp hb hr hPoly slots truth (pageCode pageWidth) (page_code_injective pageWidth pageFit)
    raw.result order nd all cert factorFit outerFit
  refine ⟨A.1,?_⟩
  change raw.steps+(legalRootWords hp hb hr m q slots raw.result).steps+8≤_
  exact Nat.add_le_add_right (Nat.add_le_add (le_of_eq fee) A.2) _
end Root

#print axioms stable_completed_count_words
end J6R25StableCensus
