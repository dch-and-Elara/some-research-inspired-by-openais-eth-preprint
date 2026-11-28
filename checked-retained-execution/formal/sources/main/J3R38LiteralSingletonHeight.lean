import J3R38LiteralSingletonReadout
import V8NativeMessageN1MainHeight

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-! The original rational layout size certificate bounds the actual
received jet, not an artificially chosen representative. This bound is
separate from the exact decoding, which requires no cost receipt. -/
namespace J3R38LiteralSingleton
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open scoped BigOperators Classical

noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

theorem original_J3_received_height (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2≤J) (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q)
    (a : Address W Q)
    (bounds : V8NativeMessage.N1.RowBound (literalTuple P R hJ Prow a) hreg R BP)
    (s : W→Bool) (k : Fin J) :
    V8NativeMessage.N1.within
      (4*Fintype.card W+(Nat.log 2 (V8NativeMessage.N1.A W R Q BP)+1)*(12*Fintype.card W)+1)
      (jetCoeff k.val (rawJet P R hJ Prow a s)) :=
  V8NativeMessage.N1.completed_bit_height (literalTuple P R hJ Prow a) hreg bounds
    s (original_menu P Prow hJ hr hR hfit a).2.2.2.1 k

#print axioms original_J3_received_height

end
end J3R38LiteralSingleton
