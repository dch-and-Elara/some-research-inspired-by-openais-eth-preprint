
import J6R31RootResidentTablesJoin
import J6R27PrescribedProbeRoot
import J6R25PreparedSupplyPhysicalPorts
import J6R26StablePreparedRootGeometry
import J6R28GeneratedRootFrameLiteral

/-! The fixed odd J6 root's actual owner selector, precision and probe
bank are the occurrence used by the publication. The exterior header
is separate from a native-prefix Ticket; the latter is not synthesized.
Production of the checked parent half-port file is a separate input. -/
namespace J6R32RootGeneratedRegistryInputs
open scoped Classical Polynomial
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R15ModeCost J6R12Repack J6R11Repack J6R10Repack J6R12Blueprint J6R11Blueprint
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R25PreparedSupply J6R21Ancestor
set_option maxHeartbeats 24000000
set_option maxRecDepth 2600
set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (J6R28GeneratedRootFrame.constantRootWord m))

noncomputable abbrev rootParentFile (ell : ℕ) (i : J6Recovery.Addr m) (wirew : ℕ) :=
  PhysicalPorts (G.selector ell) (G.ready ell) (G.centre ell i) wirew

theorem odd_site_matches_geometry (ell : ℕ) (j : J6Recovery.Addr m) :
    let c := physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m)
    let t := G.centre ell j
    packing (G.selector ell) (G.ready ell)=
      cast (congrArg (fun b=>PhysicalPacking c.host.network b (Fin 64))
        (mesh_root_bits m native G.nativeFits).symm) (rootChart T) ∧
      (centerIndex (G.ready ell) t).val=(oddAxis m).val ∧ t.val=(index m j:ℤ) ∧
      registerPrecision (rootParams f ell m native) c t=(J6SourcePrecision.printed m base) := by
  refine ⟨?_,(J6RecursiveCrossing.odd_center_valuation m j).2.1,?_,G.precision ell j⟩
  · exact exact_stable_selector_at_root base m (printedHalf m) n native (printedRankWidth m)
      T (J6R28GeneratedRootFrame.constantRootWord m) G.room G.half G.nativeFits G.rankA G.rankFit.le (G.ready ell)
  · exact oddRootCenter_value f ell base m (printedHalf m) n native T (J6R28GeneratedRootFrame.constantRootWord m) G.nativeFits j

noncomputable abbrev exteriorChild (ell : ℕ) (i : J6Recovery.Addr m)
    (j : Fin (externalProbeDegree (physicalSize m native) (physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m))+1))
    (g : Fin 64) :=
  externalZeroCall (G.selector ell) (G.ready ell) (G.centre ell i) (rootPreset G ell) j g

#print axioms odd_site_matches_geometry
end J6R32RootGeneratedRegistryInputs
