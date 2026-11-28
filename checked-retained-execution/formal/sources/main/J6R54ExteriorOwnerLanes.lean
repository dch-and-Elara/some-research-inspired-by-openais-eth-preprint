import J6R54ExteriorOwnerChart

/-! Per-half port, the R41 payload and the owner metadata are witnessed
by the very lane in the actual paid R37 emission. Atlas publication
and lane emission are distinct here; no joint execution or omitted
serialization fee is inferred from the equal header. -/
namespace J6R54ExteriorOwner
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32ChildResidentTransfer
open J6R27OriginalGate J6R53OldOwner J6R53OldOwnerRoot J6R49SourceLayout
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17500000
set_option maxRecDepth 3350
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)

theorem same_actual_outer_lane_and_owner (gate : Stamp key prec) (pad : ℕ)
    (fit : gate.created.val=base)
    (v : (Ext).host.Row⊕(Ext).host.Col) (p : PortAt (J6R34ChildPath.point (Ext).host v)) :
    let emitted := outerLanes X gate pad
    emitted.result.header=(X.seed pad).entry.result ∧
    ∃ A∈emitted.result.lanes,
      let r := if side p.val then A.packet else A.gate
      lanePayload r=initialPayload X gate pad p.val ∧
      r.origin=(exteriorData X gate pad v).origin := by
  let h : Port (RootWire m) := (edge p.val).val
  have grp : physicalGroup (G.selector ell) (G.ready ell) (G.centre ell X.centre) h=X.group :=
    (edge p.val).property
  refine ⟨actual_outer_header X gate pad,actualLane X gate pad h,selected_root_lane X gate pad h grp,
    rfl,?_⟩
  exact mounted_owner_matches_first_payload X gate pad fit v p

#print axioms same_actual_outer_lane_and_owner
end
end J6R54ExteriorOwner
