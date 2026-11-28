import J6R65LeafRatePositive

/-! A source-size envelope for leaf preparation, kept separate from
both provider execution and the actual per-packet lookup/read tariff.
Only declared bounds on physical tape/word sizes are inputs here. -/
namespace J6R65LeafRate
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 39000000
set_option maxRecDepth 4700

def printedPreparation (E V N W own key prec page gateWidth body arity : ℕ) : ℕ :=
  (bookCap W own key prec page E body+
    (3+(3*own+77)*V+(3*own+1)*V)+
    (3+V*(oldOwnerCap gateWidth W own key prec page E body E arity V+7))+5)+
  ((3+(3*page+7)*N)+bookCap W own key prec page E body+
    (3+N*(freshPageCap W key page E body+7))+7)+
  (4*V+3)+(4*E+2)+18

def zeroPreparation (totalEdges W body : ℕ) : ℕ :=
  10+2*totalEdges*(2*W+3*body+81)

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "H" => (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))

theorem true_positive_preparation_from_chart_dimensions
    (A : OwnerTerminalInput X p w Y) {width ownerWidth body arity : ℕ}
    (edgeCap : (p.ticket w).child.edges≤H)
    (word : Y.birth.port≤width) (ownerWord : Y.site.ownerWidth≤ownerWidth)
    (ancestry : observedFrameWidth A.saved.rows≤body)
    (gateArity : observedGateWidth A.roster.raw≤arity) :
    positiveSetup X p w Y A≤printedPreparation H (vertexCount (ext).host+4*(C*s)) (3*(C*s))
      width ownerWidth key prec (pageKeyWidth m+pad) (pageKeyWidth m+J6Mesh.a m) body arity := by
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  have parent : Nat.card ((p.ticket w).parent.host.Row⊕(p.ticket w).parent.host.Col)≤
      vertexCount (ext).host+4*(C*s) := by
    change Nat.card (c.host.Row⊕c.host.Col)≤_
    rw [Nat.card_sum]
    exact (actual_leaf_field_width_and_vertices (T:=T) p).2.2
  have rows : Nat.card (p.ticket w).child.host.Row≤vertexCount (ext).host+4*(C*s) :=
    (Nat.le_add_right _ _).trans (actual_leaf_field_width_and_vertices (T:=T) (Path.step p w)).2.2
  have atlas :
      Y.birth.rows.length*2^(printedParams (f:=f) (ell:=ell) s).levelBits c.depth≤3*(C*s) :=
    (actual_occurrence_compact_chart p w Y.input).1
  have cells : Y.birth.rows.length≤3*(C*s) :=
    (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))).trans atlas
  unfold positiveSetup ownerCensusFee atlasCensusFee printedPreparation
  dsimp only
  simp only [bookCap,oldOwnerCap,freshPageCap,currentGateFee,ownerDataCap,
    keptPageCap,savedGateCap,retainedScanCap,freshScanCap,emitCap,jacketCap,
    seekStride,wireFee,portOrdinalFee,missFee,hitFee,locateFee]
  gcongr

theorem true_zero_preparation_from_chart_widths {width body : ℕ}
    (word : Y.birth.port≤width) (ancestry : observedBookBodyWidth p w Y≤body) :
    zeroBookSetup p w Y≤zeroPreparation (C*s) width body := by
  unfold zeroBookSetup zeroPreparation
  gcongr

#print axioms true_positive_preparation_from_chart_dimensions
#print axioms true_zero_preparation_from_chart_widths
end
end J6R65LeafRate
