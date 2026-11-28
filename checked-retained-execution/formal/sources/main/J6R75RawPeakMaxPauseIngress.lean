import J6R75RawPeakMaxPauseScore

/-! Attach the controlled scoring cut to the same vertex pass and
to the actual already-paid ingress. Apart from a possible old
named pause, neither candidates nor different phases are added. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionGreedyStep
open J6R12CollisionGraphScore J6R12CollisionAccumulator J6R12CollisionMenu
open J6R12CollisionCandidate J6R12CollisionSource J6R12CollisionRun J6R14LayoutCost
open J6R68ActiveInputs J6R12CollisionPacking J6R10Repack P11FullPacking V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4850
set_option maxHeartbeats 24500000
set_option Elab.async false

section Literal
variable {E R C : Type*} [Fintype E] [Fintype R] [Fintype C] {a : ℕ}
variable {N : Network E R C}

def ControlledGreedyIngressWindow
    (I : Full64Input N a) (W : Ingress I)
    (pre : List (R⊕C)) (target : R⊕C) (post : List (R⊕C))
    (resident roof : ℕ) : Prop :=
    let F := I.format
    let start := initGraph F.kR F.kC W.paid.result.2
    let out := drive F.e F.kR F.kC F.b W.paid.result.1 start.result
    ∃ (first : Fin a→Fin 64) (rest : List (Fin a→Fin 64)),
      let menu := menuMachine F.b
      let seeds := literalSeed F.width F.b
      let ordered := J6R12CollisionRun.run F.width F.kR F.kC F.b F.literals (F.label first)
        (rest.map F.label)
      let previous := ordered (pre.map F.target) start.result
      let p := (J6R12CollisionRun.spec F first rest pre (fun _=>none)).1
      let choose := chooseAndWrite F.width F.kR F.kC F.b F.literals previous.result.1 (F.target target)
        (F.label first) (rest.map F.label)
      let next := ordered (post.map F.target) choose.result.1
      let held := resident+(rawLayoutBits rawLayoutTargetBits W.paid.result.1+
        rawLayoutBits rawIncidenceLayoutBits W.paid.result.2+rawLayoutBits rawEdgeLayoutBits start.result+
        gridMemoryBits menu.result+gridMemoryBits previous.result.2)
      let room := roof+candidateIngressRoom F.kR F.kC F.b I.order.length (Fintype.card E) pre.length
      out=⟨(next.result.1,previous.result.2++choose.result.2::next.result.2),
        menu.steps+seeds.steps+(previous.steps+choose.steps+next.steps+2*F.b+6)+8⟩ ∧
      previous.result.1=F.graph p ∧
      ∀ label : Fin a→Fin 64, ControlledCandidatePause F p target first rest label held room

theorem actual_greedy_layout_reuses_one_controlled_candidate_pause
    (I : Full64Input N a) (W : Ingress I)
    (pre : List (R⊕C)) (target : R⊕C) (post : List (R⊕C))
    (split : I.order=pre++target::post) (resident roof : ℕ) (live : resident≤roof) :
    ControlledGreedyIngressWindow I W pre target post resident roof := by
  let F := I.format
  let start := initGraph F.kR F.kC W.paid.result.2
  obtain ⟨first,rest,ran,prior,candidates⟩ :=
    actual_greedy_layout_candidate_after_real_target_prefix_has_pair_space I W pre target post split
      resident roof live
  refine ⟨first,rest,ran,prior,?_⟩
  intro label
  obtain ⟨real,seen⟩ := candidates label
  let ordered := J6R12CollisionRun.run F.width F.kR F.kC F.b F.literals (F.label first) (rest.map F.label)
  let previous := ordered (pre.map F.target) start.result
  let p := (J6R12CollisionRun.spec F first rest pre (fun _=>none)).1
  have eq : previous.result.1=F.graph p := prior
  exact actual_scored_candidate_uses_its_shared_control_and_tally_room F p target first rest label _ _
    (by
      change RealCandidateCall F.width F.b
        (computeCandidate F.width F.kR F.kC F.b F.literals previous.result.1 (F.target target))
        (F.label first) (rest.map F.label) (F.label label) at real
      rw [eq] at real
      exact real) seen
end Literal

#print axioms actual_greedy_layout_reuses_one_controlled_candidate_pause
end J6R75RawPeak
