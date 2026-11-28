import J6R25StableCensusRuntime

namespace J6R25StableCensus
open scoped Polynomial BigOperators Classical
open Polynomial Std.Sat P11FullPacking J6Mesh J6OrientedHost J6R23PaddingCensus J6R24LegalLayout J6R9Recursive
open J6R22RootReadout J6R18ChildWrite J6R10Integral J7R10Plant A1R10 A1R12 AOracleMachineTime
set_option maxHeartbeats 3500000
set_option maxRecDepth 2000
set_option linter.unusedSectionVars false

section Root
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

theorem exact_count_from_one_legal_chart
    (F : CNF V) (b l B R Kp : ℕ) (w : Fin (a (ms F))→Fin 64)
    (hm : ms F≤K (ms F)) (hL : 2*l=L (ms F)) (C : LegalRootChart w hm hL)
    (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (hp : 0<pm (ms F) b) (hb : 0<B) (hr : 0<R) {fw : List (Word (pm (ms F) b))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (pm (ms F) b) f)
    (slots : J6Recovery.Addr (ms F)→UVBlock fw ell)
    (received : ∀ i,J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (slots i)) =
      J6ZeroTransport.reduceAt (pm (ms F) b) (box_two_nil (pm (ms F) b) f ell)
        (chartScalar (ms F) l (qs F) (physicalPlant (inp F)) w hm hL C i))
    (code : Page (a (ms F)) (K (ms F)) (Fin 64)→ℕ) (inj : Function.Injective code)
    (raw : List (PadColumnWord Kp (a (ms F)+1))) (order : List (NativePad (ms F) l w))
    (nd : order.Nodup) (all : order.toFinset=Finset.univ)
    (chart : realizesLegalLayout (ms F) l w hm hL C code raw order)
    (factorFit : publicFactorWidth (ms F) (qs F) order.length+2≤B)
    (outerFit : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) b)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let out := legalRootWords hp hb hr m (qs F) slots raw
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
    out.steps≤legalRootBudget (pm m b) B R ell fw.length Kp m order.length := by
  exact generic_legal_root_words (ms F) l (qs F) b B R Kp (physicalPlant (inp F)) w hm hL C
    (planted_guard_zero F) (PinnedCNF.modelCount F) (exact_plain_outer_count F)
    f ell hf hF hℓ hp hb hr hPoly slots received code inj raw order nd all chart factorFit outerFit
end Root
#print axioms exact_count_from_one_legal_chart
end J6R25StableCensus
