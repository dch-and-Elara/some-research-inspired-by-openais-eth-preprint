import J6R15SignedReadRoot

/-! Connect the literal R14 only-beta-zero acquisition to the signed
readout without changing the selector, stored file, or receiving
precision. The optional physical identification below is stated before
integer lifting. -/
namespace J6R15SignedRead
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6Mesh J6OrientedHost J6R9Recursive J6R12Repack
open J6R12Blueprint J6R14ZeroMode J6R11Blueprint J1PPrinted J6OrientedHostEval
set_option maxHeartbeats 6000000

section Literal
variable {W : Type} [Fintype W] {f : ℤ[X]} {ell : ℕ}
variable (p m l q native : ℕ) (T : Plant W m q)
variable (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
variable (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
variable (hfield : f.natDegree=4*Nat.clog 2 (physicalSize m native))
variable (hsize : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize m native))
variable (hdeg : ∀ v, T.degree v≤sourceDelta (physicalSize m native))
variable (hf : f.Monic)

noncomputable def printedNativeZero (i : J6Recovery.Addr m) :
    Box f ell (J6SourcePrecision.printed m p) :=
  let sel := exactJ6Selector (f:=f) (ell:=ell) p m l q native T w mask hm hL hn
  let d := exact_j6_root_ready (f:=f) (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg
  let t := oddRootCenter f ell p m l q native T w hn i
  castBox f ell (oddRootCenter_precision f ell p m l q native T w hn i)
    (zeroRuntime sel d t hf 0)

noncomputable def printedNativeFallback (menu : Prescribed f (literalDegree m native))
    (i : J6Recovery.Addr m) : Box f ell (J6SourcePrecision.printed m p) :=
  let sel := exactJ6Selector (f:=f) (ell:=ell) p m l q native T w mask hm hL hn
  let d := exact_j6_root_ready (f:=f) (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg
  let t := oddRootCenter f ell p m l q native T w hn i
  castBox f ell (oddRootCenter_precision f ell p m l q native T w hn i)
    (fallback sel d t hf menu)

theorem printedNativeFallback_eq_direct (hF : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (menu : Prescribed f (literalDegree m native)) (i : J6Recovery.Addr m) :
    printedNativeFallback (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg hf menu i =
      printedNativeZero (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg hf i := by
  exact congrArg (castBox f ell (oddRootCenter_precision f ell p m l q native T w hn i))
    (literal_fallback_at_odd_center p m l q native T w mask hm hL hn hfield hsize hdeg hf hF menu i)

theorem acquired_layer_of_literal_zero (hF : 0<f.natDegree) (hℓ : 0<ell)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (menu : Prescribed f (literalDegree m native))
    (hz : coreA T (fun _ => false)=true)
    (ident : ∀ i, printedNativeZero (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg hf i =
      J6ZeroTransport.reduceAt _
        (J6R10Integral.box_two_nil (J6SourcePrecision.printed m p) f ell)
        (localLiteralSlot m q l T mask w hm hL i)) :
    readLayer f ell m q p l mask w hm hL hf hℓ
      (printedNativeFallback p m l q native T w mask hm hL hn hfield hsize hdeg hf menu) =
        J7R10Readout.layer m q T := by
  refine readLayer_exact f ell m q p l T mask w hm hL hf hF hℓ
    (Fintype.card_fin 64) hz _ (fun i => ?_)
  exact (printedNativeFallback_eq_direct (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg hf hF menu i).trans
    (ident i)
end Literal

#print axioms printedNativeFallback_eq_direct
#print axioms acquired_layer_of_literal_zero
end J6R15SignedRead