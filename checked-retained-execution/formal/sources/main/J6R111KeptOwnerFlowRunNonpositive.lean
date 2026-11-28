import J6R111KeptOwnerFlowRunCorrect
import J6R57PublicNoChartOnline

/-! Reuse the existing actual root/zero source code without asking for
an owner provider for unvisited branches. The retained runner executes
positive descendants directly from the entered state. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R9Recursive J6R10Reachable
open J6R50SourceProducer J6R51Online J6R52CacheWhole J6R49Leaf J6R51Leaf J6R57Public
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
set_option maxRecDepth 5400
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
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

def noPositiveProvider : OwnerInputProvider (T:=T) (pad:=pad) X :=
  fun _ _ _ _=>⟨none,0⟩

/-- For retained execution, only the root and genuinely zero descendant
cases invoke this machine's leaves. Its unused positive fallback is not
a supplier and no success/width/timing premise is imposed on it. -/
def keepOriginalNonpositiveBranches : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate :=
  withPaidOwnerLeaves X M basePos ord (noPositiveProvider (T:=T) (pad:=pad) X)

variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B)
variable (legal : ReadyOnStack (borns M) B)

theorem raw_first_and_demand_are_unmodified_for_kept_nonpositive_branches :
    (keepOriginalNonpositiveBranches X M basePos ord).initial=M.initial ∧
      (∀ {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
        (Y : StoredSite T v key prec tw bw (pageKeyWidth m+pad))
        (u : (Plan sel).Slot v.child),
        (keepOriginalNonpositiveBranches X M basePos ord).demand Y u=M.demand Y u) :=
  ⟨rfl,fun _ _=>rfl⟩

include legal live in
theorem retained_nonpositive_driver_uses_exact_original_zero_leaves :
    ZeroSourceAgreement X (keepOriginalNonpositiveBranches X M basePos ord) B := by
  intro c p w stop zero
  let R := keepOriginalNonpositiveBranches X M basePos ord
  let here := Path.step p w
  let Q := stackBank (borns M) B here
  let Y := sourceState M p w
  have bankEq : stackBank (borns R) B here=Q :=
    congrArg (fun G : Births T key prec tw bw (pageKeyWidth m+pad)=>stackBank G B here)
      (paid_owner_leaf_keeps_births X M basePos ord (noPositiveProvider (T:=T) (pad:=pad) X))
  have stack : opened (borns M) (IsLive (X.seed pad)) here Q :=
    stack_is_opened (borns M) B (IsLive (X.seed pad)) (live_monotone (X.seed pad))
      live legal here
  change (T.frame here.reached).decode (R.leafAfter p w (sourceState R p w) stop
    (stackBank (borns R) B here)).result=_
  have state : sourceState R p w=Y :=
    paid_owner_leaf_keeps_actual_source X M basePos ord (noPositiveProvider (T:=T) (pad:=pad) X) p w
  rw [bankEq,state]
  simp only [R,keepOriginalNonpositiveBranches,withPaidOwnerLeaves,if_pos zero]
  exact literal_leaf_exec_correct X pad (machineInputs X pad M) basePos here stop
    (actualEdgeOrder T (p.ticket w) Y.birth.native.physical) Q stack

include live in
theorem retained_nonpositive_driver_uses_exact_original_root_stop
    (stop : (exteriorChild G ell X.centre X.sample X.group).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff) :
    (T.frame (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group)).reached).decode
      ((keepOriginalNonpositiveBranches X M basePos ord).leafRoot stop B).result=
      (sourceBlueprint sel (exteriorChild G ell X.centre X.sample X.group) X.hf).program.run
        (exteriorChild G ell X.centre X.sample X.group) :=
  source_root_terminal_unchanged X pad (machineInputs X pad M) basePos stop ord B live

#print axioms raw_first_and_demand_are_unmodified_for_kept_nonpositive_branches
#print axioms retained_nonpositive_driver_uses_exact_original_zero_leaves
#print axioms retained_nonpositive_driver_uses_exact_original_root_stop
end
end J6R111KeptOwnerFlow

