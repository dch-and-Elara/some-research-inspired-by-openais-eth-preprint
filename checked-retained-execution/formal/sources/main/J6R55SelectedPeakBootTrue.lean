import J6R55SelectedPeakBootWriter
import J6R55BootBodiesPhysical

/-! Bind the selected boot-writer cut to the real ordered exterior
edges, the measured first-seat file, and the exact port file passed
to the first native occurrence. No old template-body list is used.
Only the named encoded fields are counted. -/
namespace J6R55SelectedPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R48RawRoute J6R11Blueprint J1PPrinted J6R24MeteredRecursion
open J6R55BootBodies J6R54PeakInput

set_option quotPrecheck false
set_option autoImplicit false
set_option maxRecDepth 3850
set_option maxHeartbeats 22000000
set_option maxSynthPendingDepth 12
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => ((Ext).host.Edge)
variable {s : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : J6R12Blueprint.Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) (exteriorChild G ell X.centre X.sample X.group)}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) (exteriorChild G ell X.centre X.sample X.group)}
variable {b : ℕ}

theorem exact_boot_source_focus_counts_generated_port_prefix
    (L : BootLaneTape X gate pad) (S : TerminalSeats X sel d t b)
    (before after : List E) (cut : orderedExteriorEdges X=before++after) (k : ℕ) :
    let lane := laneView X gate pad
    let seat := physicalSeatField (packing sel d) (centerIndex d t) S.code
    let completed : Meter (PhysicalPorts sel d t (rootHalfWidth m+1)) := readFirstPhysical X gate pad L S
    let keep := before.map (fun e=>copiedBootPair (lane e) (seat e))
    let suffix := writeBootRows (after.map lane) (after.map seat)
    writeBootRows L.run.result S.made.result=resumeBootPairCopies
      (a:=(printedParams (f:=f) (ell:=ell) s).levelBits (Ext).depth) (b:=b) keep suffix ∧
    completed.result.raw=(writeBootRows L.run.result S.made.result).result.getD [] ∧
    bootWriterFocusBits L.run.result S.made.result completed.result.raw k≤
      (L.run.result.flatMap rootLanePairBits).length+(S.made.result.flatMap physicalSeatBits).length+
        (completed.result.raw.flatMap physicalPortWords).length := by
  let lane := laneView X gate pad
  let seat := physicalSeatField (packing sel d) (centerIndex d t) S.code
  let pair := before.map (fun e=>(lane e,seat e))
  have a : L.run.result=pair.map Prod.fst++after.map lane := by
    rw [L.exact,cut,List.map_append]
    simp only [pair,List.map_map,Function.comp_def,lane]
  have b0 : S.made.result=pair.map Prod.snd++after.map seat := by
    rw [S.exact,cut,List.map_append]
    simp only [pair,List.map_map,Function.comp_def,seat]
  refine ⟨?_,rfl,actual_boot_writer_focus_is_bounded_by_full_returned_tape L.run.result S.made.result k⟩
  rw [a,b0,boot_writer_resumes_after_its_actual_paid_pairs]
  simp only [pair,List.map_map,Function.comp_def,lane,seat]

#print axioms exact_boot_source_focus_counts_generated_port_prefix
end
end J6R55SelectedPeak
