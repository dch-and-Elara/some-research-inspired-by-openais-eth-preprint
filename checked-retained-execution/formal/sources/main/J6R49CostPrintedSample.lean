import J6R49CostCoordinateBounds
import J6R25StableCensusRuntime
import J6R19RetainedScalar

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 21000000
set_option maxRecDepth 2600

/-! The archived executable chart decoder, now at the printed receiving,
factor and answer widths. The acquired U/V word is still the only
semantic input from the separate recursive machine. -/
namespace J6R49Cost
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval J6R9Recursive
open J6R23PaddingCensus J6R24LegalLayout J6R22RootReadout J6R15SignedRead
open J6R18ChildWrite J6R10Integral J6NativeHeightMesh J6R28GeneratedRootFrame
open J6R25StableCensus A1R10 A1R12 AOracleMachineTime

theorem printed_sample_exponent_le_wires (m : ℕ) (i : J6Recovery.Addr m) :
    J6Recovery.exp m i≤M m := by
  exact (Nat.sub_le _ _).trans (J6R27PrescribedProbe.mesh_length_le_edges m)

theorem actual_coordinate_fee_at_printed_widths
    {m native q base ell e : ℕ} (hn : native≤m) (hq : q≤m)
    (he : e=printedFieldWidth m native) (i : J6Recovery.Addr m) :
    let s := enlargedScale m native base ell
    makeCoordinateFee (J6SourcePrecision.printed m base) (printedFactorWidth m q)
      (printedAnswerWidth m base) ell e m (J6Recovery.exp m i)≤
      2000*(printedCoordinateScale s+1)^6 := by
  let s := enlargedScale m native base ell
  have hm : M m≤s := (source_wires_le_twice_input m native hn).trans (by unfold s enlargedScale; omega)
  have hb : base≤s := by unfold s enlargedScale; omega
  have hℓ : ell≤s := by unfold s enlargedScale; omega
  have hs : s≤printedCoordinateScale s := printed_width_in_coordinate_scale
  have hq' : q≤s := hq.trans ((Nat.le_add_right m 2).trans ((m_plus_two_le_physical_wires m).trans hm))
  have hB := (printed_factor_width_quartic hm hq').trans (Nat.mul_le_mul_right _ (by decide : 16≤64))
  apply coordinate_machine_tariff_poly (printed_precision_in_coordinate_scale hm hb) hB
    (printed_answer_width_quartic hm hb) (hℓ.trans hs) _ (hm.trans hs)
    ((printed_sample_exponent_le_wires m i).trans (hm.trans hs))
  rw [he]
  exact printed_degree_in_coordinate_scale hn hm

theorem actual_legal_chart_coordinate_polynomial {V : Type} [Fintype V]
    (base m l q native : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (hn : native≤m) (hq : q≤m)
    (i : J6Recovery.Addr m) (hz : coreA T (fun _=>false)=true)
    (f : ℤ[X]) (ell : ℕ) (hf : f.Monic) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (hfield : f.natDegree=printedFieldWidth m native)
    (hp : 0<J6SourcePrecision.printed m base) (hr : 0<printedAnswerWidth m base)
    {fw : List (Word (J6SourcePrecision.printed m base))}
    (hPoly : Modulus _ hp fw=NativeProbeRing.liftPoly (J6SourcePrecision.printed m base) f)
    (uv : UVBlock fw ell) (D : Word (printedFactorWidth m q))
    (received : J6R18ChildWrite.castBox hPoly (uvRead hp fw ell uv) =
      J6ZeroTransport.reduceAt (J6SourcePrecision.printed m base)
        (box_two_nil (J6SourcePrecision.printed m base) f ell) (chartScalar (V:=V) m l q T w hm hL C i))
    (hD : (bitsValue D.val:ℤ)=legalFactor m l q w hm hL C i) :
    let c := makeNativeCoordinate hp hr m i uv D
    c.result.realizes (sampleNum m i) (sampleDen m i) (rootOldNumerator m q T i) ∧
    c.steps≤2000*(printedCoordinateScale (enlargedScale m native base ell)+1)^6 := by
  have origin := legal_root_sample_words base m l q (printedFactorWidth m q) T w hm hL C i hz
    f ell hf hF hℓ hp hPoly uv (prepareMeshWords hp m i).result.2 D received
    (prepare_mesh_exact hp m i).2.1 hD
  have bound := make_native_coordinate_exact hp hr m i uv D (rootOldNumerator m q T i) origin
  have wDegree : fw.length=printedFieldWidth m native :=
    (J6R19Retained.size_of_monic_words hp hf hPoly).trans hfield
  exact ⟨bound.1,bound.2.trans (actual_coordinate_fee_at_printed_widths hn hq wDegree i)⟩

#print axioms printed_sample_exponent_le_wires
#print axioms actual_coordinate_fee_at_printed_widths
#print axioms actual_legal_chart_coordinate_polynomial
end J6R49Cost

