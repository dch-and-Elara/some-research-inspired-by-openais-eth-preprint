import J6R75RawPeakLayoutCandidateCache

/-! One shared candidate workspace on the literal greedy scan. At
a nonfirst candidate the declared control payload is exactly the
four named current/cache entries and one comparison flag. At the
first candidate the same reserve safely includes the one actual
entry. The tally sees the same computeCandidate closure in either
case. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionGreedyStep
open J6R12CollisionGraphScore J6R12CollisionAccumulator J6R12CollisionMenu
open J6R12CollisionCandidate J6R12CollisionSource J6R12CollisionRun J6R14LayoutCost
open J6R12CollisionPacking J6R10Repack P11FullPacking V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4600
set_option maxHeartbeats 22000000
set_option Elab.async false

def candidateControlWords (b w : ℕ) : ℕ := 4*(b+w)+1

def candidateTallyRoom (kR kC b w edges : ℕ) : ℕ :=
  let W := fullEdgeLayoutWidth kR kC b
  (2*W)*edges+(2*W)*(edges*edges)+4*w+w*(edges*edges+2)

def candidateIngressRoom (kR kC b vertices edges chosen : ℕ) :=
  (1+max kR kC)*vertices+(kR+kC)*edges+(kR+kC+2)*edges+b*2^b+b*chosen

section Score
variable {E R C A : Type*} [Fintype E] [Fintype A] [Nonempty A]

def candidateTallyPayload (F : Format E R C A) (p : R⊕C→Option A) (target : R⊕C)
    (label : A) (left : List PairTape) (x : PairTape) (right : List PairTape) : ℕ :=
  let g := F.graph p
  let new := writeGraph F.kR F.kC F.b ((F.target target).command (F.label label)) g
  let pairs := emitPairs (copyBudget F.kR F.kC F.b) new.result new.result
  let op := pairBits F.kR F.kC F.b F.width F.literals
  let terms := left.map op
  let here := op x
  let later := tally F.width op right
  let joined := scoreTallyReturn F.width here later
  let literalCost := F.literals.zero.length+F.literals.one.length+F.literals.full.length+F.literals.square.length
  rawLayoutBits rawEdgeLayoutBits g+rawLayoutBits rawEdgeLayoutBits new.result+
    rawLayoutBits pairLayoutPayload pairs.result+literalCost+
    rawLayoutBits (fun m : Meter (List Bool)=>m.result.length) terms+
    here.result.length+later.result.length+joined.result.length

def candidatePairTape (F : Format E R C A) (p : R⊕C→Option A)
    (target : R⊕C) (label : A) : List PairTape :=
  let after := writeGraph F.kR F.kC F.b ((F.target target).command (F.label label)) (F.graph p)
  (emitPairs (copyBudget F.kR F.kC F.b) after.result after.result).result

def actualLaterCandidateControls (F : Format E R C A) (p : R⊕C→Option A)
    (target : R⊕C) (first : A) (before : List A) (label : A) : ℕ :=
  let eval := computeCandidate F.width F.kR F.kC F.b F.literals (F.graph p) (F.target target)
  let initial : Entry := ⟨F.label first,(eval (F.label first)).result⟩
  let prior := scanFrom F.width F.b eval initial (before.map F.label)
  let score := eval (F.label label)
  let comparison := compareBits score.result prior.result.score
  let now : Entry := ⟨F.label label,score.result⟩
  let keep := if comparison.result then now else prior.result
  layoutEntryWidth initial+layoutEntryWidth prior.result+layoutEntryWidth now+layoutEntryWidth keep+1

def ControlledCandidatePause (F : Format E R C A) (p : R⊕C→Option A) (target : R⊕C)
    (first : A) (rest : List A) (label : A) (held room : ℕ) : Prop :=
  let eval := computeCandidate F.width F.kR F.kC F.b F.literals (F.graph p) (F.target target)
  let reserve := candidateControlWords F.b F.width
  let upper := room+reserve+candidateTallyRoom F.kR F.kC F.b F.width (Fintype.card E)
  RealCandidateCall F.width F.b eval (F.label first) (rest.map F.label) (F.label label) ∧
  ActualCandidateWorkspace F p target label held room ∧
  ∃ controls : ℕ,
    ((label=first ∧ controls=layoutEntryWidth ⟨F.label first,(eval (F.label first)).result⟩) ∨
      ∃ prior suffix,rest=prior++label::suffix ∧ controls=actualLaterCandidateControls F p target first prior label) ∧
    controls≤reserve ∧
    ∀ left x right,candidatePairTape F p target label=left++x::right →
      let paused := held+controls+candidateTallyPayload F p target label left x right
      paused≤upper ∧
      ∀ oldBits oldRoof,oldBits≤oldRoof → max oldBits paused≤max oldRoof upper

private theorem candidate_label_injective (F : Format E R C A) :
    Function.Injective F.label := by
  intro a b h
  have eq := congrArg bitsValue h
  change bitsValue (encodeBits F.b (F.aCode a)) = bitsValue (encodeBits F.b (F.aCode b)) at eq
  rw [encodeBits_exact _ _ (F.aFit a),encodeBits_exact _ _ (F.aFit b)] at eq
  exact F.aInj eq

private theorem split_at_present_candidate (lst : List A) (a : A) (h : a∈lst) :
    ∃ left right,lst=left++a::right := by
  induction lst with
  | nil=>simp at h
  | cons v vs ih=>
    rcases List.mem_cons.mp h with same|hit
    · subst v
      exact ⟨[],vs,rfl⟩
    · obtain ⟨left,right,eq⟩ := ih hit
      exact ⟨v::left,right,congrArg (v::·) eq⟩

theorem actual_scored_candidate_uses_its_shared_control_and_tally_room
    (F : Format E R C A) (p : R⊕C→Option A) (target : R⊕C) (first : A)
    (rest : List A) (label : A) (held room : ℕ)
    (real : RealCandidateCall F.width F.b
      (computeCandidate F.width F.kR F.kC F.b F.literals (F.graph p) (F.target target))
      (F.label first) (rest.map F.label) (F.label label))
    (seen : ActualCandidateWorkspace F p target label held room) :
    ControlledCandidatePause F p target first rest label held room := by
  let eval := computeCandidate F.width F.kR F.kC F.b F.literals (F.graph p) (F.target target)
  let reserve := candidateControlWords F.b F.width
  have state : ∃ controls : ℕ,
    ((label=first ∧ controls=layoutEntryWidth ⟨F.label first,(eval (F.label first)).result⟩) ∨
      ∃ prior suffix,rest=prior++label::suffix ∧ controls=actualLaterCandidateControls F p target first prior label) ∧
    controls≤reserve := by
    rcases real with initial|⟨front,back,hit,_⟩
    · have eq := candidate_label_injective F initial.1
      let firstW := layoutEntryWidth ⟨F.label first,(eval (F.label first)).result⟩
      have width : firstW=F.b+F.width := congrArg₂ (·+·)
        (encodeBits_length _ _) ((F.candidate_exact p target first).1)
      exact ⟨firstW,Or.inl ⟨eq,rfl⟩,by unfold reserve candidateControlWords; omega⟩
    · have isIn : F.label label∈rest.map F.label := hit.symm ▸ List.mem_append_right _ List.mem_cons_self
      obtain ⟨which,inside,same⟩ := List.mem_map.mp isIn
      have eq := candidate_label_injective F same
      subst which
      obtain ⟨pre,next,whereAt⟩ := split_at_present_candidate rest label inside
      let control := actualLaterCandidateControls F p target first pre label
      have bound : control=reserve := by
        exact (one_actual_candidate_keeps_cached_control_words_in_the_pair_workspace
          F p target first pre label next 0 0 (Nat.le_refl _)).2.1
      exact ⟨control,Or.inr ⟨pre,next,whereAt,rfl⟩,bound.le⟩
  obtain ⟨controls,exact,controlFit⟩ := state
  refine ⟨real,seen,controls,exact,controlFit,?_⟩
  intro left x right split
  have tallyFit : held+candidateTallyPayload F p target label left x right≤
      room+candidateTallyRoom F.kR F.kC F.b F.width (Fintype.card E) :=
    (seen.2.2.2.2 left x right split).2
  have cap := Nat.add_le_add tallyFit controlFit
  rw [Nat.add_right_comm] at cap
  rw [Nat.add_right_comm room] at cap
  exact ⟨cap,fun _ _ h=>max_le_max h cap⟩
end Score

#print axioms actual_scored_candidate_uses_its_shared_control_and_tally_room
end J6R75RawPeak
