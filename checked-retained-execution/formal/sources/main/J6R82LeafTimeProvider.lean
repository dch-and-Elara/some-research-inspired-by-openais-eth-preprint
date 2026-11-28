import J6R65LeafRatePositive

/-! The R65 positive branch accepts a paid structural supplier.
Same exact output tables do not bound its Meter: the logical supplier
interface accepts an arbitrary additional charge, paid once. -/
namespace J6R82LeafTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 35000000
set_option maxRecDepth 5000

private theorem finish_positive_adds_cost {f : ℤ[X]} {q ell : ℕ}
    (F : Frame f q) (m : Meter (Option (Block F ell))) (extra : ℕ) :
    finishOwnerAttempt F (padCost m extra)=padCost (finishOwnerAttempt F m) extra := by
  cases m with
  | mk val fee =>
    cases val <;> simp only [finishOwnerAttempt,padCost] <;> congr 1 <;> omega

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
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (provider : OwnerInputProvider (T:=T) (pad:=pad) X)

def delayedProvider (delay : ℕ) : OwnerInputProvider (T:=T) (pad:=pad) X :=
  fun {_} p w Y stop=>padCost (provider p w Y stop) delay

theorem delayed_owner_provider_keeps_every_input
    (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate) (delay : ℕ) :
    HasMeasuredOwnerInputs X M (delayedProvider X provider delay)↔HasMeasuredOwnerInputs X M provider :=
  Iff.rfl

variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))

theorem run_true_positive_uses_added_provider_fee_once
    (stop : ((Plan sel).child c w).edges≤(SP).cutoff) (B : Bank) (delay : ℕ) :
    runOwnerPositive X (delayedProvider X provider delay) p w Y stop B=
      padCost (runOwnerPositive X provider p w Y stop B) delay := by
  let F := T.frame (Path.step p w).reached
  let attempt := provider p w Y stop
  unfold runOwnerPositive
  dsimp only [delayedProvider]
  cases h : attempt.result with
  | none =>
    have e : (provider p w Y stop).result=none := h
    simp only [padCost,e]
    congr 1
    omega
  | some A =>
    have e : (provider p w Y stop).result=some A := h
    have eq :
        executeOwnerTerminal X p w Y ⟨A,attempt.steps+delay⟩ F B=
          padCost (executeOwnerTerminal X p w Y ⟨A,attempt.steps⟩ F B) delay := by
      unfold executeOwnerTerminal padCost
      dsimp only
      congr 1
      omega
    have ed : (padCost (provider p w Y stop) delay).result=some A := e
    rw [ed]
    change finishOwnerAttempt F (executeOwnerTerminal X p w Y ⟨A,attempt.steps+delay⟩ F B)=
      padCost (finishOwnerAttempt F (executeOwnerTerminal X p w Y ⟨A,attempt.steps⟩ F B)) delay
    rw [eq,finish_positive_adds_cost]

variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)

theorem unchanged_positive_source_cannot_bound_an_arbitrary_owner_provider
    (initial : Bank) (stop : ((Plan sel).child c w).edges≤(SP).cutoff)
    (positive : 0<((Plan sel).child c w).edges)
    (ready : HasMeasuredOwnerInputs X M provider) (n : ℕ) :
    let before := readLeaf (withPaidOwnerLeaves X M basePos ord provider) initial (.step p w) stop
    let shifted : OwnerInputProvider (T:=T) (pad:=pad) X :=
      fun {_} path slot site h=>delayedProvider X provider (n+1) path slot site h
    let later := readLeaf (withPaidOwnerLeaves X M basePos ord shifted) initial (.step p w) stop
    HasMeasuredOwnerInputs X M shifted ∧
    (shifted p w (sourceState M p w) stop).result=(provider p w (sourceState M p w) stop).result ∧
    later.result=before.result ∧ later.steps=before.steps+(n+1) ∧ n<later.steps := by
  have d := J6R62Leaf.read_leaf_uses_positive_owner_runtime X p w M basePos ord
    (delayedProvider X provider (n+1)) initial stop positive
  have o := J6R62Leaf.read_leaf_uses_positive_owner_runtime X p w M basePos ord
    provider initial stop positive
  have e := run_true_positive_uses_added_provider_fee_once X provider p w (sourceState M p w)
    stop (stackBank (borns M) initial (.step p w)) (n+1)
  dsimp only
  rw [d,o,e]
  exact ⟨ready,rfl,rfl,rfl,by simp only [padCost]; omega⟩

#print axioms delayed_owner_provider_keeps_every_input
#print axioms run_true_positive_uses_added_provider_fee_once
#print axioms unchanged_positive_source_cannot_bound_an_arbitrary_owner_provider
end
end J6R82LeafTime
