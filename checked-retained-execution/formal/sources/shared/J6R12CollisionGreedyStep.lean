import J6R12CollisionCandidate
import J6R12CollisionGraphScore

/-!
# One genuine conditional-expectation step on the graph tape

For each candidate, copy and relabel the same original edge tape by a
sequential pass, then run the metered ordered-pair score. Ties preserve
the first minimum. Commit exactly the winning candidate by another
sequential pass. The returned label is a literal bit word.
-/

namespace J6R12CollisionGreedyStep
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R11CollisionCost J6R11CollisionCostSelect
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionGraphScore
open J6R12CollisionCandidate

inductive Target
  | row (id : List Bool)
  | col (id : List Bool)

def Target.command (t : Target) (lab : List Bool) : RegisterWrite :=
  match t with
  | .row i => .row i lab
  | .col i => .col i lab

def computeCandidate (w kR kC b : ℕ) (L : Literals) (es : List EdgeTape)
    (q : Target) (lab : List Bool) : Meter (List Bool) :=
  let G := writeGraph kR kC b (q.command lab) es
  let s := scoreGraph w kR kC b L G.result
  ⟨s.result,G.steps+s.steps+8⟩

def chooseAndWrite (w kR kC b : ℕ) (L : Literals) (es : List EdgeTape)
    (q : Target) (first : List Bool) (rest : List (List Bool)) : Meter (List EdgeTape × List Bool) :=
  let S := computeCandidate w kR kC b L es q
  let win := scanMenu w b S first rest
  let G := writeGraph kR kC b (q.command win.result.label) es
  ⟨(G.result,win.result.label),win.steps+G.steps+8⟩

structure Format (E R C A : Type*) [Fintype E] [Fintype A] where
  e : ℕ
  kR : ℕ
  kC : ℕ
  b : ℕ
  rCode : R→ℕ
  cCode : C→ℕ
  aCode : A→ℕ
  rInj : Function.Injective rCode
  cInj : Function.Injective cCode
  aInj : Function.Injective aCode
  rFit : ∀ i, rCode i<2^kR
  cFit : ∀ i, cCode i<2^kC
  aFit : ∀ i, aCode i<2^b
  edgesFit : Fintype.card E<2^e
  alphabetFit : Fintype.card A≤2^b
  row : E→R
  col : E→C
  edges : List E
  edgesNodup : edges.Nodup
  edgesAll : ∀ i : E, i ∈ edges

namespace Format
variable {E R C A : Type*} [Fintype E] [Fintype A]

def width (F : Format E R C A) : ℕ := scoreWidth F.e F.b

def literals (F : Format E R C A) : Literals := makeLiterals F.width (Fintype.card A)

def label (F : Format E R C A) (a : A) : List Bool := encodeBits F.b (F.aCode a)

def target (F : Format E R C A) (q : R⊕C) : Target :=
  match q with
  | .inl i => .row (encodeBits F.kR (F.rCode i))
  | .inr i => .col (encodeBits F.kC (F.cCode i))

def graph (F : Format E R C A) (p : R⊕C→Option A) : List EdgeTape :=
  F.edges.map (packEdge F.kR F.kC F.b F.rCode F.cCode F.aCode F.row F.col p)

def writeBound (F : Format E R C A) : ℕ :=
  (writeBudget F.kR F.kC F.b+6)*Fintype.card E

def candidateBound (F : Format E R C A) : ℕ :=
  F.writeBound+scoreGraphBudget F.width F.kR F.kC F.b (Fintype.card E)+8

def stepBound (F : Format E R C A) (n : ℕ) : ℕ :=
  (F.candidateBound+12*F.width+2*F.b+8)*n+F.writeBound+8

theorem graphEdges (F : Format E R C A) : F.edges.length=Fintype.card E := by
  rw [← List.toFinset_card_of_nodup F.edgesNodup]
  have hset : F.edges.toFinset=Finset.univ := by ext e; simp [F.edgesAll e]
  rw [hset,Finset.card_univ]

theorem command_exact (F : Format E R C A) (q : R⊕C) (lab : A) :
    (F.target q).command (F.label lab) = encodeWrite F.kR F.kC F.b F.rCode F.cCode F.aCode q lab := by
  cases q <;> rfl

theorem commit_exact (F : Format E R C A) (p : R⊕C→Option A) (q : R⊕C) (a : A) :
    let z := writeGraph F.kR F.kC F.b ((F.target q).command (F.label a)) (F.graph p)
    z.result=F.graph (Function.update p q (some a)) ∧ z.steps≤F.writeBound := by
  rw [F.command_exact]
  unfold graph writeBound
  rw [← F.graphEdges]
  exact writeGraph_exact F.kR F.kC F.b F.rCode F.cCode F.aCode F.rInj F.cInj F.rFit F.cFit
    F.row F.col p q a F.edges

variable [Nonempty A]

theorem score_no_overflow (F : Format E R C A) (p : R⊕C→Option A) :
    integerScore F.row F.col p < 2^F.width := by
  have H := integerScore_register F.row F.col p F.e F.b F.edgesFit F.alphabetFit
  unfold width scoreWidth
  rw [pow_succ]
  exact H.trans_le (by omega)

theorem candidate_exact (F : Format E R C A) (p : R⊕C→Option A) (q : R⊕C) (a : A) :
    let z := computeCandidate F.width F.kR F.kC F.b F.literals (F.graph p) (F.target q) (F.label a)
    z.result.length=F.width ∧
      bitsValue z.result=integerScore F.row F.col (Function.update p q (some a)) ∧
      z.steps≤F.candidateBound := by
  let u := Function.update p q (some a)
  let g := writeGraph F.kR F.kC F.b ((F.target q).command (F.label a)) (F.graph p)
  have hg : g.result=F.graph u ∧ g.steps≤F.writeBound := F.commit_exact p q a
  obtain ⟨h1,hb,hbb⟩ := scoreWidth_fits (Fintype.card A) F.e F.b F.alphabetFit
  have H := scoreGraph_exact F.width F.kR F.kC F.b F.rCode F.cCode F.aCode
    F.rInj F.cInj F.aInj F.rFit F.cFit F.aFit h1 hb hbb F.row F.col u F.edges F.edgesNodup
    F.edgesAll (F.score_no_overflow u)
  let s := scoreGraph F.width F.kR F.kC F.b F.literals (F.graph u)
  have hs : s.result.length=F.width ∧ bitsValue s.result=integerScore F.row F.col u ∧
    s.steps≤scoreGraphBudget F.width F.kR F.kC F.b (Fintype.card E) := H
  change (scoreGraph F.width F.kR F.kC F.b F.literals g.result).result.length=F.width ∧
    bitsValue (scoreGraph F.width F.kR F.kC F.b F.literals g.result).result=integerScore F.row F.col u ∧
    g.steps+(scoreGraph F.width F.kR F.kC F.b F.literals g.result).steps+8≤F.candidateBound
  rw [hg.1]
  exact ⟨hs.1,hs.2.1,Nat.add_le_add_right (Nat.add_le_add hg.2 hs.2.2) 8⟩

noncomputable def winner (F : Format E R C A) (p : R⊕C→Option A) (q : R⊕C)
    (first : A) (rest : List A) : A :=
  (minimumEntry (fun a => integerScore F.row F.col (Function.update p q (some a))) first rest).1

theorem step_exact (F : Format E R C A) (p : R⊕C→Option A) (q : R⊕C)
    (first : A) (rest : List A) :
    let z := chooseAndWrite F.width F.kR F.kC F.b F.literals (F.graph p) (F.target q)
      (F.label first) (rest.map F.label)
    let a := F.winner p q first rest
    z.result.1=F.graph (Function.update p q (some a)) ∧ z.result.2=F.label a ∧
      z.steps≤F.stepBound (rest.length+1) := by
  let eval := computeCandidate F.width F.kR F.kC F.b F.literals (F.graph p) (F.target q)
  let score := fun a => integerScore F.row F.col (Function.update p q (some a))
  let win := scanMenu F.width F.b eval (F.label first) (rest.map F.label)
  let a := F.winner p q first rest
  obtain ⟨hlabel,_hWidth,_hScore,hbudget⟩ :=
    scanMenu_exact F.width F.b F.candidateBound F.label score eval
      (fun a => F.candidate_exact p q a) first rest
  change win.result.label=F.label a at hlabel
  change win.steps≤_ at hbudget
  let g := writeGraph F.kR F.kC F.b ((F.target q).command win.result.label) (F.graph p)
  have H : g.result=F.graph (Function.update p q (some a)) ∧ g.steps≤F.writeBound := by
    unfold g
    rw [hlabel]
    exact F.commit_exact p q a
  exact ⟨H.1,hlabel,Nat.add_le_add_right (Nat.add_le_add hbudget H.2) 8⟩

variable [Fintype R] [Fintype C]
theorem winner_greedy (F : Format E R C A) (p : R⊕C→Option A) (q : R⊕C)
    (first : A) (rest : List A) (hAll : ∀ a, a ∈ first::rest) :
    integerScore F.row F.col (Function.update p q (some (F.winner p q first rest))) ≤
      integerScore F.row F.col p := next_nonincreasing F.row F.col p q first rest hAll

#print axioms graphEdges
#print axioms commit_exact
#print axioms score_no_overflow
#print axioms candidate_exact
#print axioms step_exact
#print axioms winner_greedy

end Format
end J6R12CollisionGreedyStep
