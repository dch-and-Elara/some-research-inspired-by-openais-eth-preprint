import J6R75RawPeakLayoutCandidate
import J6R75RawPeakStockGrid
import J6R75RawPeakLayoutJob

/-! Exact prefixes of the actual greedy vertex run and its candidate
scan. A candidate is scored on the actual rewritten input at its
target, not a second layout's graph with the same integer score. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionGraphScore
open J6R12CollisionAccumulator J6R12CollisionMenu J6R12CollisionSource J6R12CollisionRun
open J6R12CollisionCandidate J6R12CollisionPacking J6R14LayoutCost J6R68ActiveInputs
open J6R10Repack P11FullPacking V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16100000
set_option maxRecDepth 4800
set_option Elab.async false

theorem actual_greedy_prefix_reuses_its_own_committed_graph
    (w kR kC b : ℕ) (L : Literals) (first : List Bool) (menu : List (List Bool))
    (pre post : List Target) (g : List EdgeTape) :
    let doRun := J6R12CollisionRun.run w kR kC b L first menu
    let before := doRun pre g
    let after := doRun post before.result.1
    doRun (pre++post) g=
      ⟨(after.result.1,before.result.2++after.result.2),before.steps+after.steps⟩ := by
  induction pre generalizing g with
  | nil=>simp [J6R12CollisionRun.run]
  | cons t ts ih=>
    let step := chooseAndWrite w kR kC b L g t first menu
    let run := J6R12CollisionRun.run w kR kC b L first menu
    let X := run ts step.result.1
    let Y := run post X.result.1
    change (⟨((run (ts++post) step.result.1).result.1,
        step.result.2::(run (ts++post) step.result.1).result.2),
        step.steps+(run (ts++post) step.result.1).steps+2*b+6⟩ :
      Meter (List EdgeTape×List (List Bool)))=
      ⟨(Y.result.1,(step.result.2::X.result.2)++Y.result.2),
        step.steps+X.steps+2*b+6+Y.steps⟩
    have ran := ih step.result.1
    change run (ts++post) step.result.1=
      ⟨(Y.result.1,X.result.2++Y.result.2),X.steps+Y.steps⟩ at ran
    rw [ran]
    exact congrArg (Meter.mk (Y.result.1,step.result.2::(X.result.2++Y.result.2))) (by
      change step.steps+(X.steps+Y.steps)+2*b+6=step.steps+X.steps+2*b+6+Y.steps
      omega)

private def nextScanBest (eval : List Bool→Meter (List Bool)) (best : Entry)
    (lab : List Bool) : Entry :=
  let x := eval lab
  let q := compareBits x.result best.score
  if q.result then ⟨lab,x.result⟩ else best

theorem actual_layout_candidates_reenter_their_same_cached_best
    (w b : ℕ) (eval : List Bool→Meter (List Bool)) (best : Entry)
    (pre post : List (List Bool)) :
    let prior := scanFrom w b eval best pre
    let suffix := scanFrom w b eval prior.result post
    scanFrom w b eval best (pre++post)=⟨suffix.result,prior.steps+suffix.steps⟩ := by
  induction pre generalizing best with
  | nil=>simp [scanFrom]
  | cons lab ls ih=>
    let score := eval lab
    let compare := compareBits score.result best.score
    let chosen := nextScanBest eval best lab
    let prior := scanFrom w b eval chosen ls
    let suffix := scanFrom w b eval prior.result post
    change (⟨(scanFrom w b eval chosen (ls++post)).result,
      score.steps+compare.steps+(scanFrom w b eval chosen (ls++post)).steps+2*w+2*b+8⟩ :
      Meter Entry)=⟨suffix.result,score.steps+compare.steps+prior.steps+2*w+2*b+8+suffix.steps⟩
    have ran := ih chosen
    change scanFrom w b eval chosen (ls++post)=⟨suffix.result,prior.steps+suffix.steps⟩ at ran
    rw [ran]
    exact congrArg (Meter.mk suffix.result) (by
      change score.steps+compare.steps+(prior.steps+suffix.steps)+2*w+2*b+8=
        score.steps+compare.steps+prior.steps+2*w+2*b+8+suffix.steps
      omega)

theorem actual_nonfirst_candidate_is_evaluated_after_that_precise_prefix
    (w b : ℕ) (eval : List Bool→Meter (List Bool)) (first : List Bool)
    (pre : List (List Bool)) (current : List Bool) (post : List (List Bool)) :
    let begin := eval first
    let prior := scanFrom w b eval ⟨first,begin.result⟩ pre
    let score := eval current
    let compare := compareBits score.result prior.result.score
    let keep := if compare.result then ⟨current,score.result⟩ else prior.result
    let suffix := scanFrom w b eval keep post
    scanMenu w b eval first (pre++current::post)=
      ⟨suffix.result,begin.steps+prior.steps+score.steps+compare.steps+suffix.steps+4*w+4*b+16⟩ := by
  dsimp only [scanMenu]
  rw [actual_layout_candidates_reenter_their_same_cached_best]
  dsimp only [scanFrom]
  congr 1
  omega

section Native
variable {E R C : Type*} [Fintype E] [Fintype R] [Fintype C] {a : ℕ}
variable {N : Network E R C}

theorem literal_layout_greedy_source_has_the_named_intermediate_target
    (I : Full64Input N a) (W : Ingress I)
    (pre : List (R⊕C)) (target : R⊕C) (post : List (R⊕C))
    (split : I.order=pre++target::post) :
    let F := I.format
    let start := initGraph F.kR F.kC W.paid.result.2
    let out := drive F.e F.kR F.kC F.b W.paid.result.1 start.result
    ∃ (first : Fin a→Fin 64) (rest : List (Fin a→Fin 64)),
      let menu := (menuMachine F.b)
      let seeds := literalSeed F.width F.b
      let ordered := J6R12CollisionRun.run F.width F.kR F.kC F.b F.literals (F.label first)
        (rest.map F.label)
      let previous := ordered (pre.map F.target) start.result
      let choose := chooseAndWrite F.width F.kR F.kC F.b F.literals previous.result.1 (F.target target)
        (F.label first) (rest.map F.label)
      let next := ordered (post.map F.target) choose.result.1
      menu.result=F.label first::rest.map F.label ∧ seeds.result=F.literals ∧
      previous.result.1=F.graph (J6R12CollisionRun.spec F first rest pre (fun _=>none)).1 ∧
      (∀ label : Fin a→Fin 64,label=first∨label∈rest) ∧
      out=⟨(next.result.1,previous.result.2++choose.result.2::next.result.2),
        menu.steps+seeds.steps+(previous.steps+choose.steps+next.steps+2*F.b+6)+8⟩ := by
  let F := I.format
  let start := initGraph F.kR F.kC W.paid.result.2
  have n : Fintype.card (Fin a→Fin 64)=2^F.b := by
    rw [show F.b=6*a from I.labelWidth,source_alphabet (G:=Fin 64) (by simp) a]
  obtain ⟨first,rest,menu,_,complete,_⟩ := full_alphabet F n
  have want : (literalSeed F.width F.b).result=F.literals := by
    rw [Format.literals,n]
    exact literalSeed_exact _ _ (by unfold Format.width scoreWidth; omega)
  have raw : start.result=F.graph (fun _=>none) := by
    unfold start
    rw [W.incidences]
    exact (initGraph_exact I.format).1
  have prefixReceipt : (J6R12CollisionRun.run F.width F.kR F.kC F.b F.literals (F.label first)
      (rest.map F.label) (pre.map F.target) start.result).result.1=
      F.graph (J6R12CollisionRun.spec F first rest pre (fun _=>none)).1 := by
    rw [raw]
    exact (run_exact F first rest pre (fun _=>none)).1
  refine ⟨first,rest,menu,want,prefixReceipt,fun label=>List.mem_cons.mp (complete label),?_⟩
  unfold drive
  dsimp only
  rw [show scoreWidth F.e F.b=F.width from rfl,menu,want,W.commands,split,List.map_append,List.map_cons]
  dsimp only
  rw [actual_greedy_prefix_reuses_its_own_committed_graph]
  dsimp only [J6R12CollisionRun.run,F]
  congr 1
  omega
end Native

#print axioms actual_greedy_prefix_reuses_its_own_committed_graph
#print axioms actual_layout_candidates_reenter_their_same_cached_best
#print axioms actual_nonfirst_candidate_is_evaluated_after_that_precise_prefix
#print axioms literal_layout_greedy_source_has_the_named_intermediate_target
end J6R75RawPeak
