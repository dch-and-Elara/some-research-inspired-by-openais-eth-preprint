import J6R75RawPeakLayoutIngress
import J6R12CollisionAccumulator

/-! A real greedy candidate emits the entire ordered pair record tape
before scoring it. The bound keeps that source-emitted table and
the actual earlier tally words; no streaming rewrite, pair quotient,
or allocator interpretation is substituted. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionGraphScore
open J6R12CollisionAccumulator J6R12CollisionMenu J6R14LayoutCost

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13500000
set_option maxRecDepth 4400
set_option Elab.async false

def pairLayoutPayload (x : PairTape) : ℕ :=
  rawEndLayoutBits x.r₁+rawEndLayoutBits x.r₂+rawEndLayoutBits x.c₁+rawEndLayoutBits x.c₂

theorem actual_layout_pair_bits_add_its_two_incidence_widths (v w : EdgeTape) :
    pairLayoutPayload (pair v w)=rawEdgeLayoutBits v+rawEdgeLayoutBits w := by
  unfold pairLayoutPayload pair rawEdgeLayoutBits
  ac_rfl

def scoreTallyReturn (w : ℕ) (x tail : Meter (List Bool)) : Meter (List Bool) :=
  let a := addBits x.result tail.result
  ⟨a.result,x.steps+tail.steps+a.steps+2*w+8⟩

theorem real_layout_pair_tally_reenters_its_actual_prefix {A : Type*} 
    (w : ℕ) (term : A→Meter (List Bool)) (pre : List A) (x : A) (tail : List A) :
    tally w term (pre++x::tail)=
      (pre.map term).foldr (scoreTallyReturn w) (scoreTallyReturn w (term x) (tally w term tail)) := by
  induction pre with
  | nil=>rfl
  | cons t ts ih=>exact congrArg (scoreTallyReturn w (term t)) ih

private theorem fixed_score_term_tally_length {A : Type*} (w : ℕ) (f : A→Meter (List Bool))
    (each : ∀ x,(f x).result.length=w) (xs : List A) :
    (tally w f xs).result.length=w := by
  induction xs with
  | nil=>simp [tally]
  | cons x xs ih=>
    change (addBits (f x).result (tally w f xs).result).result.length=w
    exact (addBits_exact _ _ ((each x).trans ih.symm)).1.trans (each x)

section Source
variable {E R C A : Type*} [Fintype E] [Fintype A] [Nonempty A]

theorem partial_source_graph_keeps_all_occurrences_at_the_same_layout_width
    (F : Format E R C A) (p : R⊕C→Option A) :
    (F.graph p).length=Fintype.card E ∧
    (∀ x∈F.graph p,rawEdgeLayoutBits x≤fullEdgeLayoutWidth F.kR F.kC F.b) ∧
    rawLayoutBits rawEdgeLayoutBits (F.graph p)≤fullEdgeLayoutWidth F.kR F.kC F.b*Fintype.card E := by
  have count : (F.graph p).length=Fintype.card E := by simp [Format.graph,F.graphEdges]
  have row (x : EdgeTape) (hit : x∈F.graph p) : rawEdgeLayoutBits x≤fullEdgeLayoutWidth F.kR F.kC F.b := by
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hit
    unfold rawEdgeLayoutBits rawEndLayoutBits packEdge packEnd
    cases le : p (.inl (F.row e)) <;> cases re : p (.inr (F.col e)) <;>
      simp only [le,re,fullEdgeLayoutWidth,encodeBits_length,Option.map_some,Option.getD_some,
        Option.map_none,Option.getD_none] <;> omega
  exact ⟨count,row,(raw_layout_bits_le_of_field_cap _ _ _ row).trans_eq (congrArg (_*·) count)⟩

theorem true_candidate_materializes_real_pair_records_and_selected_tally_words
    (F : Format E R C A) (p : R⊕C→Option A) (target : R⊕C) (label : A)
    (resident roof : ℕ) (live : resident≤roof) :
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
      roof+((2*W)*M+(2*W)*(M*M)+4*K+K*(M*M+2)) := by
  let g := F.graph p
  let u := Function.update p target (some label)
  let new := writeGraph F.kR F.kC F.b ((F.target target).command (F.label label)) g
  let pairs := emitPairs (copyBudget F.kR F.kC F.b) new.result new.result
  let K := F.width
  let op := pairBits F.kR F.kC F.b K F.literals
  let M := Fintype.card E
  let W := fullEdgeLayoutWidth F.kR F.kC F.b
  have actual : new.result=F.graph u := (F.commit_exact p target label).1
  have old := partial_source_graph_keeps_all_occurrences_at_the_same_layout_width F p
  have nxt := partial_source_graph_keeps_all_occurrences_at_the_same_layout_width F u
  have count : new.result.length=M := (congrArg List.length actual).trans nxt.1
  have made := (emitPairs_exact (copyBudget F.kR F.kC F.b) new.result new.result).1
  have prodLen (l r : List EdgeTape) : (l.product r).length=l.length*r.length := by
    induction l with
    | nil=>simp [List.product]
    | cons x xs ih=>simp [List.product,Nat.succ_mul,Nat.add_comm]
  have c : pairs.result.length=M*M := by rw [made,List.length_map,prodLen,count]
  have field (r : PairTape) (hit : r∈pairs.result) : pairLayoutPayload r≤2*W := by
    change r∈(emitPairs _ new.result new.result).result at hit
    rw [made] at hit
    obtain ⟨ef,hep,rfl⟩ := List.mem_map.mp hit
    obtain ⟨front,back⟩ := List.mem_product.mp hep
    rw [actual_layout_pair_bits_add_its_two_incidence_widths]
    have f : rawEdgeLayoutBits ef.1≤W := nxt.2.1 _ (actual ▸ front)
    have b : rawEdgeLayoutBits ef.2≤W := nxt.2.1 _ (actual ▸ back)
    omega
  have table : rawLayoutBits pairLayoutPayload pairs.result≤(2*W)*(M*M) :=
    (raw_layout_bits_le_of_field_cap _ _ _ field).trans_eq (congrArg ((2*W)*·) c)
  have width (x : PairTape) : (op x).result.length=K := by
    obtain ⟨a,b,c⟩ := scoreWidth_fits (Fintype.card A) F.e F.b F.alphabetFit
    exact (termBits_exact K (Fintype.card A) a b c
      (sideTape F.kR F.b x.r₁ x.r₂).result (sideTape F.kC F.b x.c₁ x.c₂).result).1
  refine ⟨rfl,actual,c,table,?_⟩
  intro pre x tail split
  have exactSplit : pairs.result=pre++x::tail := split
  have runs : tally K op pairs.result=(pre.map op).foldr (scoreTallyReturn K)
      (scoreTallyReturn K (op x) (tally K op tail)) := by
    rw [exactSplit]
    exact real_layout_pair_tally_reenters_its_actual_prefix K op pre x tail
  have a : pre.length+1≤M*M := by
    rw [exactSplit,List.length_append,List.length_cons] at c
    omega
  have oldNow : rawLayoutBits rawEdgeLayoutBits new.result≤W*M := by
    rw [actual]; exact nxt.2.2
  have bits :
    rawLayoutBits (fun m : Meter (List Bool)=>m.result.length) (pre.map op)=K*pre.length := by
    rw [raw_layout_bits_fixed _ _ _ (fun t h=>by
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp h
      exact width y),List.length_map]
  have q := fixed_score_term_tally_length K op width tail
  have result : (scoreTallyReturn K (op x) (tally K op tail)).result.length=K := by
    change (addBits (op x).result (tally K op tail).result).result.length=K
    exact (addBits_exact _ _ ((width x).trans q.symm)).1.trans (width x)
  have lit : F.literals.zero.length+F.literals.one.length+F.literals.full.length+
      F.literals.square.length=4*K := by
    simp only [Format.literals,makeLiterals,encodeBits_length,K]
    omega
  refine ⟨runs,Nat.add_le_add live ?_⟩
  change rawLayoutBits rawEdgeLayoutBits g+rawLayoutBits rawEdgeLayoutBits new.result+
    rawLayoutBits pairLayoutPayload pairs.result+_+
    rawLayoutBits (fun m : Meter (List Bool)=>m.result.length) (pre.map op)+
    (op x).result.length+(tally K op tail).result.length+
    (scoreTallyReturn K (op x) (tally K op tail)).result.length≤_
  rw [lit,bits,width x,q,result]
  change rawLayoutBits rawEdgeLayoutBits g+rawLayoutBits rawEdgeLayoutBits new.result+
    rawLayoutBits pairLayoutPayload pairs.result+4*K+K*pre.length+K+K+K≤
      (2*W)*M+(2*W)*(M*M)+4*K+K*(M*M+2)
  have oldFit : rawLayoutBits rawEdgeLayoutBits g≤W*M := old.2.2
  have rightCount : K*(pre.length+1)≤K*(M*M) := Nat.mul_le_mul_left _ a
  rw [Nat.mul_succ] at rightCount
  have gfit : rawLayoutBits rawEdgeLayoutBits g+rawLayoutBits rawEdgeLayoutBits new.result≤(2*W)*M := by
    have f := Nat.add_le_add oldFit oldNow
    rwa [←two_mul (W*M),←Nat.mul_assoc] at f
  calc
    _ = (rawLayoutBits rawEdgeLayoutBits g+rawLayoutBits rawEdgeLayoutBits new.result+
        rawLayoutBits pairLayoutPayload pairs.result+4*K)+(K*pre.length+K+K+K) := by ac_rfl
    _ ≤ ((2*W)*M+(2*W)*(M*M)+4*K)+(K*(M*M)+K+K) :=
      Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add gfit table) _)
        (Nat.add_le_add_right (Nat.add_le_add_right rightCount _) _)
    _ = _ := by ring
end Source

#print axioms actual_layout_pair_bits_add_its_two_incidence_widths
#print axioms real_layout_pair_tally_reenters_its_actual_prefix
#print axioms partial_source_graph_keeps_all_occurrences_at_the_same_layout_width
#print axioms true_candidate_materializes_real_pair_records_and_selected_tally_words
end J6R75RawPeak
