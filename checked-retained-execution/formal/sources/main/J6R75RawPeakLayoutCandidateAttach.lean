import J6R75RawPeakLayoutCandidatePath

/-! Same raw layout ingress, actual target prefix and candidate
lookup. The working bound follows the real graph, not merely an
equal chosen label or completed layout. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionGraphScore
open J6R12CollisionAccumulator J6R12CollisionMenu J6R14LayoutCost

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18600000
set_option maxRecDepth 4400
set_option Elab.async false

open J6R12CollisionMenu J6R12CollisionSource J6R12CollisionRun J6R12CollisionCandidate
open J6R12CollisionPacking J6R68ActiveInputs J6R10Repack P11FullPacking
open V8NativeMessage.N2DLabels

def ActualCandidateWorkspace {E R C A : Type*} [Fintype E] [Fintype A]
    (F : Format E R C A) (p : R⊕C→Option A) (target : R⊕C) (label : A)
    (resident roof : ℕ) : Prop :=
  let g := F.graph p
  let new := writeGraph F.kR F.kC F.b ((F.target target).command (F.label label)) g
  let pairs := emitPairs (copyBudget F.kR F.kC F.b) new.result new.result
  let score := scoreTape F.width F.kR F.kC F.b F.literals pairs.result
  let op := pairBits F.kR F.kC F.b F.width F.literals
  let M := Fintype.card E
  let W := fullEdgeLayoutWidth F.kR F.kC F.b
  let K := F.width
  let literalCost := F.literals.zero.length+F.literals.one.length+F.literals.full.length+F.literals.square.length
  computeCandidate F.width F.kR F.kC F.b F.literals g (F.target target) (F.label label)=
    ⟨score.result,new.steps+((pairs.steps+score.steps+8))+8⟩ ∧
  new.result=F.graph (Function.update p target (some label)) ∧
  pairs.result.length=M*M ∧
  rawLayoutBits pairLayoutPayload pairs.result≤(2*W)*(M*M) ∧
  ∀ pre x tail,pairs.result=pre++x::tail →
    let earlier := pre.map op
    let later := tally K op tail
    let here := op x
    let joined := scoreTallyReturn K here later
    score=earlier.foldr (scoreTallyReturn K) joined ∧
    resident+(rawLayoutBits rawEdgeLayoutBits g+rawLayoutBits rawEdgeLayoutBits new.result+
      rawLayoutBits pairLayoutPayload pairs.result+literalCost+
      rawLayoutBits (fun m : Meter (List Bool)=>m.result.length) earlier+
      here.result.length+later.result.length+joined.result.length)≤
    roof+((2*W)*M+(2*W)*(M*M)+4*K+K*(M*M+2))

private theorem spec_labels_count {E R C A : Type*} [Fintype E] [Fintype A] [Nonempty A]
    (F : Format E R C A) (first : A) (rest : List A)
    (pre : List (R⊕C)) (p : R⊕C→Option A) :
    (J6R12CollisionRun.spec F first rest pre p).2.length=pre.length := by
  induction pre generalizing p with
  | nil=>rfl
  | cons x xs ih=>simp [J6R12CollisionRun.spec,ih]

private theorem take_candidate_at_hit {T : Type*} (xs : List T) (x : T) (h : x∈xs) :
    ∃ pre post,xs=pre++x::post := by
  induction xs with
  | nil=>simp at h
  | cons y ys ih=>
    rcases List.mem_cons.mp h with same|later
    · subst y
      exact ⟨[],ys,rfl⟩
    · obtain ⟨pre,post,eq⟩ := ih later
      exact ⟨y::pre,post,congrArg (y::·) eq⟩

def RealCandidateCall (w b : ℕ) (eval : List Bool→Meter (List Bool)) (first : List Bool)
    (aliases : List (List Bool)) (candidate : List Bool) : Prop :=
  (candidate=first ∧
    scanMenu w b eval first aliases=
      let start := eval candidate
      let next := scanFrom w b eval ⟨first,start.result⟩ aliases
      ⟨next.result,start.steps+next.steps+2*w+2*b+8⟩) ∨
  ∃ pre post,aliases=pre++candidate::post ∧
    let start := eval first
    let before := scanFrom w b eval ⟨first,start.result⟩ pre
    let now := eval candidate
    let compare := compareBits now.result before.result.score
    let keep := if compare.result then ⟨candidate,now.result⟩ else before.result
    let suffix := scanFrom w b eval keep post
    scanMenu w b eval first aliases=
      ⟨suffix.result,start.steps+before.steps+now.steps+compare.steps+suffix.steps+4*w+4*b+16⟩

section Literal
variable {E R C : Type*} [Fintype E] [Fintype R] [Fintype C] {a : ℕ}
variable {N : Network E R C}

theorem actual_greedy_layout_candidate_after_real_target_prefix_has_pair_space
    (I : Full64Input N a) (W : Ingress I)
    (pre : List (R⊕C)) (target : R⊕C) (post : List (R⊕C)) (split : I.order=pre++target::post)
    (resident roof : ℕ) (live : resident≤roof) :
    let F := I.format
    let start := initGraph F.kR F.kC W.paid.result.2
    let out := drive F.e F.kR F.kC F.b W.paid.result.1 start.result
    ∃ (first : Fin a→Fin 64) (rest : List (Fin a→Fin 64)),
      let menu := (menuMachine F.b)
      let seeds := literalSeed F.width F.b
      let ordered := J6R12CollisionRun.run F.width F.kR F.kC F.b F.literals (F.label first)
        (rest.map F.label)
      let previous := ordered (pre.map F.target) start.result
      let p := (J6R12CollisionRun.spec F first rest pre (fun _=>none)).1
      let choose := chooseAndWrite F.width F.kR F.kC F.b F.literals previous.result.1 (F.target target)
        (F.label first) (rest.map F.label)
      let next := ordered (post.map F.target) choose.result.1
      let score := computeCandidate F.width F.kR F.kC F.b F.literals previous.result.1 (F.target target)
      let held := resident+(rawLayoutBits rawLayoutTargetBits W.paid.result.1+
        rawLayoutBits rawIncidenceLayoutBits W.paid.result.2+rawLayoutBits rawEdgeLayoutBits start.result+
        gridMemoryBits menu.result+gridMemoryBits previous.result.2)
      let room := roof+((1+max F.kR F.kC)*I.order.length+(F.kR+F.kC)*Fintype.card E+
        (F.kR+F.kC+2)*Fintype.card E+F.b*2^F.b+F.b*pre.length)
      out=⟨(next.result.1,previous.result.2++choose.result.2::next.result.2),
        menu.steps+seeds.steps+(previous.steps+choose.steps+next.steps+2*F.b+6)+8⟩ ∧
      previous.result.1=F.graph p ∧
      ∀ label : Fin a→Fin 64,
        RealCandidateCall F.width F.b score (F.label first) (rest.map F.label) (F.label label) ∧
        ActualCandidateWorkspace F p target label held room := by
  let F := I.format
  let start := initGraph F.kR F.kC W.paid.result.2
  have raw : start.result=F.graph (fun _=>none) := by
    unfold start
    rw [W.incidences]
    exact (initGraph_exact I.format).1
  obtain ⟨first,rest,menu,_,workingGraph,complete,go⟩ :=
    literal_layout_greedy_source_has_the_named_intermediate_target I W pre target post split
  let ordered := J6R12CollisionRun.run F.width F.kR F.kC F.b F.literals (F.label first) (rest.map F.label)
  let previous := ordered (pre.map F.target) start.result
  let p := (J6R12CollisionRun.spec F first rest pre (fun _=>none)).1
  let score := computeCandidate F.width F.kR F.kC F.b F.literals previous.result.1 (F.target target)
  have written : previous.result.2=(J6R12CollisionRun.spec F first rest pre (fun _=>none)).2.map F.label := by
    unfold previous
    rw [raw]
    exact (run_exact F first rest pre (fun _=>none)).2.1
  have wordSize : gridMemoryBits previous.result.2=F.b*pre.length := by
    rw [written,uniform_grid_bits F.b _ (fun x hx=>by
      obtain ⟨s,_,rfl⟩ := List.mem_map.mp hx
      exact encodeBits_length _ _),List.length_map,spec_labels_count]
  obtain ⟨commands,wires,before⟩ := actual_ingress_commands_and_wire_bytes_have_their_source_capacity I W
  have heldFit : rawLayoutBits rawLayoutTargetBits W.paid.result.1+
      rawLayoutBits rawIncidenceLayoutBits W.paid.result.2+rawLayoutBits rawEdgeLayoutBits start.result+
      gridMemoryBits (menuMachine F.b).result+gridMemoryBits previous.result.2≤
      (1+max F.kR F.kC)*I.order.length+(F.kR+F.kC)*Fintype.card E+
        (F.kR+F.kC+2)*Fintype.card E+F.b*2^F.b+F.b*pre.length := by
    rw [wires,show rawLayoutBits rawEdgeLayoutBits start.result=_ from before,
      emitted_menu_grid_bit_width_is_exact,wordSize]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right commands _) _) _) _
  refine ⟨first,rest,go,workingGraph,?_⟩
  intro label
  refine ⟨?_,true_candidate_materializes_real_pair_records_and_selected_tally_words
    F p target label _ _ (Nat.add_le_add live heldFit)⟩
  rcases complete label with eq|hit
  · subst label
    exact Or.inl ⟨rfl,rfl⟩
  · obtain ⟨past,future,whereAt⟩ := take_candidate_at_hit rest label hit
    refine Or.inr ⟨past.map F.label,future.map F.label,?_,?_⟩
    · have cut := congrArg (List.map F.label) whereAt
      simpa only [List.map_append,List.map_cons] using cut
    · let pool := past.map F.label++F.label label::future.map F.label
      have eq : rest.map F.label=pool := by
        dsimp only [pool]
        simpa only [List.map_append,List.map_cons] using congrArg (List.map F.label) whereAt
      change scanMenu F.width F.b score (F.label first) (rest.map F.label)=_
      exact (congrArg (scanMenu F.width F.b score (F.label first)) eq).trans
        (actual_nonfirst_candidate_is_evaluated_after_that_precise_prefix
          F.width F.b score (F.label first) (past.map F.label) (F.label label) (future.map F.label))
end Literal

#print axioms actual_greedy_layout_candidate_after_real_target_prefix_has_pair_space
end J6R75RawPeak
