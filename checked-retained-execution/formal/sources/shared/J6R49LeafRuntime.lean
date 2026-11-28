import J6R49LeafSource

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22000000
set_option maxRecDepth 3400

/-! Thin leaf ABI for a runner using an already paid physical edge
ordinals. Compare the final raw leaf sum to the literal stopped source
program, without pretending the order is the model's equivFin. -/
namespace J6R49Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6Mesh J6OrientedHost P11FullPacking P1DyadicGrid J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R11Repack J6R12Blueprint J6R21Ancestor J6R20Ancestor
open J6R14ZeroMode J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R27OriginalGate J6R9PacketScopes
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R34RootAtlas J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R22Active J6R35RootOrigins J6R48Leaf
open J6R9Recursive J6R10Reachable J6R24MeteredRecursion J6R21Leaf J6R16ModeCost
noncomputable section

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
theorem true_source_stops_on_same_host [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
    (P : Prepared cfg sel r hf)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (stop : c.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff) :
    reduce c.prec f ell (c.host.contract hf)=(sourceBlueprint sel r hf).program.run c := by
  let B := sourceBlueprint sel r hf
  have spec : B.entries=physicalEntries hf := rfl
  have hc : c.edges≤(paddedShape (N sel) (Childs sel) r).cutoff := stop
  change _=B.program.run c
  rw [Program.run,dif_pos hc]
  change _=B.leaf c
  rw [Blueprint.leaf_exact,physicalBlueprint_truth hf B spec c (planEdges (T:=P) path)]

variable {V : Type} [Fintype V]
variable {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {S : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
local notation "ext" => exteriorChild G ell X.centre X.sample X.group
local notation "pgWidth" => pageKeyWidth m+pad
local notation "SP" => printedParams (f:=f) (ell:=ell) s
variable (I : InputFamily S key prec tw bw (pageKeyWidth m+pad))

def literalLeafExec (basePos : 0<base) {c : Call (PhysicalHost f ell)}
    (p : Path sel ext c) (_stop : c.edges≤(SP).cutoff) (ord : Fin c.edges≃c.host.Edge)
    (B : PageBank f ell key prec tw bw pgWidth) : Meter (Block (S.frame p.reached) ell) :=
  runTape (sourceLeafTape X pad I basePos p ord) X.hf (S.frame p.reached) S.vPositive B

set_option maxHeartbeats 27000000 in
theorem literal_leaf_exec_correct
    [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) ext)]
    (basePos : 0<base) {c : Call (PhysicalHost f ell)}
    (p : Path sel ext c) (stop : c.edges≤(SP).cutoff) (ord : Fin c.edges≃c.host.Edge)
    (B : PageBank f ell key prec tw bw pgWidth)
    (run : opened (compileFamily I) (IsLive (X.seed pad)) p B) :
    (S.frame p.reached).decode (literalLeafExec X pad I basePos p stop ord B).result=
      (sourceBlueprint sel ext X.hf).program.run c :=
  (literal_leaf_all_orders X pad I basePos p ord B run).1.trans
    (true_source_stops_on_same_host S p stop)

#print axioms true_source_stops_on_same_host
#print axioms literalLeafExec
#print axioms literal_leaf_exec_correct
end
end J6R49Leaf
