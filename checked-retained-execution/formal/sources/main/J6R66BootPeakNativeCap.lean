import J6R66BootPeakAtlas
import J6R34RootAtlasGeometry

/-! The previous Page bound can be discharged for the original exterior
using its genuine row/column subscans, code words, and finite roster.
No unrelated cap oracle or upper bound on arbitrary source encodings. -/
namespace J6R66.BootPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R17ModeTape J6R32RootGeneratedRegistryInputs J6R54PeakInput J6R55SelectedPeak J6R24MeteredRecursion
open J6R48DFS J6R33PageIndexedBirth J6R33StatefulArithmeticPage J6R21Ancestor
open J6R30ProducedGateRegistry J6R51Peak P11FullPacking
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15500000
set_option maxRecDepth 4800
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec key bw tc tj tw edgew : ℕ}
variable (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)

def realRootModeCount : ℕ :=
  (rootPreparationFor X).result.resident.roster.modes.length

def actualExteriorPageCap : ℕ :=
  ell*(f.natDegree*J6SourcePrecision.printed m base)+M m*a m+M m*a m+
     realRootModeCount X*(X.code+1+J6SourcePrecision.printed m base+2+q)

theorem all_real_exterior_pages_fit_the_actual_mode_and_port_roof :
    ∀ y∈rootTable X.chosenFields,(originPayload y.payload).length≤actualExteriorPageCap X := by
  intro y hy
  unfold rootTable at hy
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hy
  let F := X.chosenFields k
  obtain ⟨r,c,_,_,_,_,ξ,ms,modes,_,code⟩ := stable_seed_true_page_law X k
  have rowLen : F.rows.length≤M m := by
    rw [show F.rows=_ from r,List.length_map,←actual_wires_count m]
    unfold sourceRows scanSubtype
    exact List.length_filterMap_le _ _
  have colLen : F.cols.length≤M m := by
    rw [show F.cols=_ from c,List.length_map,←actual_wires_count m]
    unfold sourceCols scanSubtype
    exact List.length_filterMap_le _ _
  have modeLen : F.modes.length≤realRootModeCount X := by
    rw [show F.modes=_ from modes,List.length_ofFn]
    exact le_rfl
  have len : ∀ μ∈F.modes,μ.code.length≤X.code := by
    intro μ hm
    rw [show F.modes=_ from modes] at hm
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm
    rw [code j,AOracleMachineTimeTape.encodeBits_length]
  have fit := explicit_page_payload_bound F (M m) (M m) (realRootModeCount X) X.code rowLen colLen
    modeLen len
  rw [X.field.result.natDegree X.hf] at fit
  exact fit

theorem real_external_atlas_cut_with_explicit_native_payload
    (S : ActualRootPreparation G ell q) (same : S=(rootPreparationFor X).result)
    (pad ri ni wi : ℕ) :
    let req := exteriorPageRequests X
    let native := rootTable X.chosenFields
    let job := preparedSeed X S same pad
    let U := actualExteriorPageCap X
    bitSize pageRequestBits (req.result.take ri)+bitSize atlasRowBits (native.take ni)+
      bitSize atlasRowBits (job.expected.pages.take wi)≤
      pagesCount (a m) (K m)*
        ((6*a m+6*a m+q+pageKeyWidth m)+(pageKeyWidth m+U)+(pageKeyWidth m+pad+U)) :=
  (actual_exterior_atlas_mount_cut_bits X S same pad (actualExteriorPageCap X)
    (all_real_exterior_pages_fit_the_actual_mode_and_port_roof X) ri ni wi).2.2

#print axioms actualExteriorPageCap
#print axioms all_real_exterior_pages_fit_the_actual_mode_and_port_roof
#print axioms real_external_atlas_cut_with_explicit_native_payload
end
end J6R66.BootPeak
