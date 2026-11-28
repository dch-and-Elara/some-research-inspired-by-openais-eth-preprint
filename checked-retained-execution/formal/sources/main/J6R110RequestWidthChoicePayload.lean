import J6R110RequestWidthChoiceNumeric
import J6R54PublicFamilyWords
import J6R57PublicRequestBounds
import J6R110RootWidthChoiceProducer

/-! Apply the selected widths to the unmodified R54/R57 paid head,
actual binary entry fields and exterior child's edge-count word.
A head fee is not a full oracle query or field-inspection fee. -/
namespace J6R110RequestWidthChoice
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6Mesh J6OrientedHost J6R15ModeCost
open J6R24LegalLayout J6R26StablePreparedRoot J6R28GeneratedRootFrame
open J6R14ZeroMode J6R27PrescribedProbe J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R54PublicFamily J6R57PublicRequest
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option maxRecDepth 3300
set_option maxHeartbeats 16000000

def chosenHeadSourceRoof (s : ℕ) : ℕ :=
  ordinalFee (2*s+1) (4*s)+ordinalFee (4*s+2) (8*s^2)+(6*(2*s+1)+5)+6

theorem chosen_head_clock_is_bounded_by_source_roof (m native : ℕ) (nativeFit : native≤m) :
    headRoof m native (centreWidth m) (sampleWidth m) (magnitudeWidth m)≤
      chosenHeadSourceRoof (physicalSize m native) := by
  let s := physicalSize m native
  have dim := true_request_dimensions_polynomial m native nativeFit
  have w := chosen_request_widths_polynomial_bounds m native nativeFit
  have sample : literalDegree m native≤8*s^2 := by
    have d : literalDegree m native+1≤8*s^2+1 := dim.2.2
    omega
  have read1 := J6R110RootWidthChoice.ordinal_fee_mono_dimensions w.1 dim.2.1
  have read2 := J6R110RootWidthChoice.ordinal_fee_mono_dimensions w.2.1 sample
  have copy : 2*centreWidth m+4*magnitudeWidth m+5≤6*(2*s+1)+5 := by
    have hc : centreWidth m≤2*s+1 := w.1
    have hm : magnitudeWidth m≤2*s+1 := w.2.2.1
    omega
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add read1 read2) copy) 6

theorem chosen_registered_key_has_polynomial_width (m native kp : ℕ) (nativeFit : native≤m) :
    KeyWidth kp (centreWidth m) (sampleWidth m)≤kp+6*physicalSize m native+9 := by
  have w := chosen_request_widths_polynomial_bounds m native nativeFit
  have hc : centreWidth m≤2*physicalSize m native+1 := w.1
  have hj : sampleWidth m≤4*physicalSize m native+2 := w.2.1
  unfold KeyWidth
  omega

theorem actual_selected_head_has_exact_numbers_and_polynomial_fee
    (m native : ℕ) (nativeFit : native≤m)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) :
    let H := prepareHead (chooseWidths m native nativeFit) i j
    H.result.data.centre.val=index m i ∧ H.result.data.sample.val=j.val ∧
      H.result.data.magnitude.val=index m i ∧
      H.steps=ordinalFee (centreWidth m) (index m i)+ordinalFee (sampleWidth m) j.val+
        (2*centreWidth m+4*magnitudeWidth m+5)+6 ∧
      H.steps≤chosenHeadSourceRoof (physicalSize m native) := by
  let s := physicalSize m native
  let W := chooseWidths m native nativeFit
  let H := prepareHead W i j
  have fee := query_head_exact_fee W i j
  have dims := true_request_dimensions_polynomial m native nativeFit
  have widths := chosen_request_widths_polynomial_bounds m native nativeFit
  have centre : index m i≤2*m+1 := by have hit := i.isLt; unfold index; omega
  have sample : j.val≤8*s^2 := by
    have hi := j.isLt
    have hj : literalDegree m native+1≤8*s^2+1 := dims.2.2
    omega
  have read1 := J6R110RootWidthChoice.ordinal_fee_mono_dimensions widths.1 (centre.trans dims.2.1)
  have read2 := J6R110RootWidthChoice.ordinal_fee_mono_dimensions widths.2.1 sample
  have copy : 2*centreWidth m+4*magnitudeWidth m+5≤6*(2*s+1)+5 := by
    have ht : centreWidth m≤2*s+1 := widths.1
    have hw : magnitudeWidth m≤2*s+1 := widths.2.2.1
    omega
  refine ⟨H.result.centreOK,H.result.sampleOK,H.result.magnitudeOK,fee,?_⟩
  change H.steps≤chosenHeadSourceRoof s
  change H.steps=_ at fee
  rw [fee]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add read1 read2) copy) 6

theorem actual_selected_entry_preserves_original_address_fields
    (m native : ℕ) (nativeFit : native≤m) {kp : ℕ}
    (mark : Word kp) (x : Coordinate m native) :
    let E := (emitAt (chooseWidths m native nativeFit) mark x).result
    E.coord=x ∧ E.wire.centre.val=index m x.1.1 ∧ E.wire.sample.val=x.1.2.val ∧
      E.wire.group.val=x.2.val ∧ E.id=(issueExterior mark E.wire).result ∧
      E.id.bits.length=kp+3*lambda m+9 := by
  let E := (emitAt (chooseWidths m native nativeFit) mark x).result
  obtain ⟨coordinate,i,j,g,key,_⟩ := actual_entry_wires (chooseWidths m native nativeFit) mark x
  exact ⟨coordinate,i,j,g,key,E.id.size.trans (chosen_marked_key_width m kp)⟩

noncomputable section Edge
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n native base : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem selected_edge_lane_fits_the_true_exterior_child
    (nativeFit : native≤m) (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
    let child := exteriorChild G ell i j g
    let w := word (q:=edgeWidth m) child.edges
    child.edges<2^edgeWidth m ∧ w.val=child.edges ∧ w.bits.length=edgeWidth m := by
  have fit := (exterior_edge_count_le (G:=G) (ell:=ell) i j g).trans_lt
    (chooseWidths m native nativeFit).edgeFit
  exact ⟨fit,word_val fit,(word (q:=edgeWidth m) (exteriorChild G ell i j g).edges).size⟩

end Edge
#print axioms chosen_head_clock_is_bounded_by_source_roof
#print axioms chosen_registered_key_has_polynomial_width
#print axioms actual_selected_head_has_exact_numbers_and_polynomial_fee
#print axioms actual_selected_entry_preserves_original_address_fields
#print axioms selected_edge_lane_fits_the_true_exterior_child
end J6R110RequestWidthChoice

