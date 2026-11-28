import J6R57PublicNoChartLeaf
import J6R53OldOwnerHeaders

namespace J6R57Public
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}

variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))

theorem owner_terminal_tables_are_exact_source_lists
    (A : OwnerTerminalInput X p w Y) :
    A.saved.rows=(halfOrder T (p.ticket w) Y.birth.native.physical).map Y.site.frame ∧
      A.headers.raw=A.headers.order.map (ownerGroupRow Y.site) ∧
      A.roster.raw=A.roster.order.map (fun x =>
        ⟨Y.site.oldKey x,parentData Y (gateHistory T (bootGates X) p) x⟩) ∧
      (A.headers.order.Nodup ∧ ∀ x,x∈A.headers.order) ∧
      (A.roster.order.Nodup ∧ ∀ x,x∈A.roster.order) := by
  have written := (true_site_issuance Y.site).2.2.2
  exact ⟨Option.some.inj (A.saved.exactRows.symm.trans written),A.headers.same,A.roster.exactRows,
    ⟨A.headers.unique,A.headers.all⟩,⟨A.roster.unique,A.roster.complete⟩⟩

variable (cache : Meter (CachedParentFrames Y.site))
variable (owners : Meter (CompleteRoster Y.site.oldKey (parentData Y (gateHistory T (bootGates X) p))))
variable (groups : Meter (List (J6R15ModeCost.Word 6)))
variable (align : groups.result=owners.result.order.map (fun x=>(ownerGroupRow Y.site x).group))
variable (inj : Function.Injective Y.site.oldKey)

/-- Actual once-paid preparation of the input consumed by the positive
terminal. Exact matches require a measured group tape and owner roster,
not an arbitrary raw header line list. -/
def packMeasuredOwnerInput : Meter (OwnerTerminalInput X p w Y) :=
  let H := useCompleteRoster Y (parentData Y (gateHistory T (bootGates X) p))
    owners.result groups.result align
  ⟨⟨cache.result,H.result,owners.result,inj⟩,cache.steps+owners.steps+groups.steps+H.steps+5⟩

theorem pack_preserves_the_actual_tables_and_exact_fees :
    let H := useCompleteRoster Y (parentData Y (gateHistory T (bootGates X) p))
      owners.result groups.result align
    let K := packMeasuredOwnerInput X p w Y cache owners groups align inj
    K.result.saved=cache.result ∧ K.result.headers=H.result ∧
      K.result.roster=owners.result ∧ K.steps=cache.steps+owners.steps+groups.steps+H.steps+5 :=
  ⟨rfl,rfl,rfl,rfl⟩

#print axioms owner_terminal_tables_are_exact_source_lists
#print axioms packMeasuredOwnerInput
#print axioms pack_preserves_the_actual_tables_and_exact_fees
end
end J6R57Public
