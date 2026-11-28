import J6R12CollisionGreedyStep

/-!
# Complete metered vertex-by-vertex conditional-expectation loop

No label table is queried at unit cost. The edge tape is scanned and
updated in the candidate evaluator and then in the winning commit.
The final output also lists a word for every scheduled vertex,
including isolated vertices. Input conversion and the later sorting
and packet construction are not part of this machine.
-/

namespace J6R12CollisionRun
open scoped BigOperators Classical
open AOracleMachineTime
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionGreedyStep
open J6R11Collision J6R11CollisionCost J6R11CollisionGreedy DiagonalAbundance

def run (w kR kC b : ℕ) (L : Literals) (first : List Bool) (rest : List (List Bool)) :
    List Target → List EdgeTape → Meter (List EdgeTape × List (List Bool))
  | [],g => ⟨(g,[]),0⟩
  | q::qs,g =>
    let step := chooseAndWrite w kR kC b L g q first rest
    let more := run w kR kC b L first rest qs step.result.1
    ⟨(more.result.1,step.result.2::more.result.2),step.steps+more.steps+2*b+6⟩

variable {E R C A : Type*} [Fintype E] [Fintype A] [Nonempty A]

noncomputable def spec (F : Format E R C A) (first : A) (rest : List A) :
    List (R⊕C) → (R⊕C→Option A) → (R⊕C→Option A) × List A
  | [],p => (p,[])
  | q::qs,p =>
    let a := F.winner p q first rest
    let s := spec F first rest qs (Function.update p q (some a))
    (s.1,a::s.2)

theorem run_exact (F : Format E R C A) (first : A) (rest : List A)
    (vs : List (R⊕C)) (p : R⊕C→Option A) :
    let z := run F.width F.kR F.kC F.b F.literals (F.label first) (rest.map F.label)
      (vs.map F.target) (F.graph p)
    let P := spec F first rest vs p
    z.result.1=F.graph P.1 ∧ z.result.2=P.2.map F.label ∧
      z.steps≤(F.stepBound (rest.length+1)+2*F.b+6)*vs.length := by
  induction vs generalizing p with
  | nil => simp [run,spec]
  | cons q qs ih =>
    let a := F.winner p q first rest
    let p' := Function.update p q (some a)
    let step := chooseAndWrite F.width F.kR F.kC F.b F.literals (F.graph p)
      (F.target q) (F.label first) (rest.map F.label)
    have hs : step.result.1=F.graph p' ∧ step.result.2=F.label a ∧
      step.steps≤F.stepBound (rest.length+1) := F.step_exact p q first rest
    obtain ⟨hg,hl,hc⟩ := ih p'
    let s := run F.width F.kR F.kC F.b F.literals (F.label first) (rest.map F.label)
      (qs.map F.target)
    change (s step.result.1).result.1=F.graph (spec F first rest qs p').1 ∧
      step.result.2::(s step.result.1).result.2 =
        F.label a::(spec F first rest qs p').2.map F.label ∧
      step.steps+(s step.result.1).steps+2*F.b+6≤(F.stepBound (rest.length+1)+2*F.b+6)*(qs.length+1)
    rw [hs.1,hs.2.1]
    refine ⟨hg,by rw [hl],?_⟩
    change (s (F.graph p')).steps≤_ at hc
    rw [Nat.mul_succ]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hs.2.2 hc) (2*F.b)) 6
      |>.trans_eq (by ac_rfl)

omit [Nonempty A] in
theorem spec_absent (F : Format E R C A) (first : A) (rest : List A)
    (vs : List (R⊕C)) (p : R⊕C→Option A) (i : R⊕C) (hi : i ∉ vs) :
    (spec F first rest vs p).1 i=p i := by
  induction vs generalizing p with
  | nil => rfl
  | cons q qs ih =>
    have hq : i≠q := fun h => hi (List.mem_cons.mpr (Or.inl h))
    have hs : i∉qs := fun h => hi (List.mem_cons_of_mem _ h)
    simp only [spec]
    rw [ih _ hs,Function.update_of_ne hq]

omit [Nonempty A] in
theorem spec_retains (F : Format E R C A) (first : A) (rest : List A)
    (vs : List (R⊕C)) (p : R⊕C→Option A) (i : R⊕C) (h : ∃ a, p i=some a) :
    ∃ a, (spec F first rest vs p).1 i=some a := by
  induction vs generalizing p with
  | nil => exact h
  | cons q qs ih =>
    apply ih
    by_cases he : i=q
    · subst i
      simp
    · rw [Function.update_of_ne he]
      exact h

omit [Nonempty A] in
theorem spec_total_on_schedule (F : Format E R C A) (first : A) (rest : List A)
    (vs : List (R⊕C)) (p : R⊕C→Option A) (i : R⊕C) (hi : i ∈ vs) :
    ∃ a, (spec F first rest vs p).1 i=some a := by
  induction vs generalizing p with
  | nil => simp at hi
  | cons q qs ih =>
    simp only [spec]
    rcases List.mem_cons.mp hi with rfl|h
    · exact spec_retains F first rest qs _ i (by simp)
    · exact ih _ h

omit [Nonempty A] in
theorem spec_trace (F : Format E R C A) (first : A) (rest : List A) (vs : List (R⊕C))
    (p : R⊕C→Option A) (hn : vs.Nodup) :
    (spec F first rest vs p).2.map some = vs.map (spec F first rest vs p).1 := by
  induction vs generalizing p with
  | nil => rfl
  | cons q qs ih =>
    obtain ⟨habs,ht⟩ := List.nodup_cons.mp hn
    let a := F.winner p q first rest
    let p' := Function.update p q (some a)
    have he := spec_absent F first rest qs p' q habs
    have hh : (spec F first rest qs p').1 q=some a := he.trans (by simp [p'])
    change some a :: (spec F first rest qs p').2.map some =
      (spec F first rest qs p').1 q :: qs.map (spec F first rest qs p').1
    rw [hh,ih p' ht]

variable [Fintype R] [Fintype C]

theorem spec_nonincreasing (F : Format E R C A) (first : A) (rest : List A) (vs : List (R⊕C))
    (p : R⊕C→Option A) (hAll : ∀ a : A, a ∈ first::rest) :
    integerScore F.row F.col (spec F first rest vs p).1 ≤ integerScore F.row F.col p := by
  induction vs generalizing p with
  | nil => rfl
  | cons q qs ih =>
    exact (ih (Function.update p q (some (F.winner p q first rest)))).trans (F.winner_greedy p q first rest hAll)

theorem compressed_full (row : E→R) (col : E→C) (z : R⊕C→A) :
    compressed row col (marginal (fun i => some (z i))) =
      J1MainSourceCollision.deviation (edgeCell row col (splitSample z)) := by
  let f : (R⊕C→A)→ℚ := fun s =>
    J1MainSourceCollision.deviation (edgeCell row col (splitSample s))
  have hfix : marginal (fun i => some (z i)) =
      GuardExpectation.fixOn (marginal (fun _ : R⊕C => (none : Option A))) Finset.univ z := by
    funext i a
    simp [marginal,GuardExpectation.fixOn]
  let w := marginal (fun i => some (z i))
  have hc : GuardExpectation.average w f=compressed row col w :=
    compressed_correct row col w (marginal_normalized _)
  rw [← hc]
  change GuardExpectation.average (marginal (fun i => some (z i))) f=f z
  rw [hfix,GuardExpectation.average_fixOn_univ]

theorem compressed_initial (row : E→R) (col : E→C) (Δ : ℕ)
    (hr : ∀ v, (fibre row v).card≤Δ) (hc : ∀ v, (fibre col v).card≤Δ) :
    compressed row col (marginal (fun _ : R⊕C => (none : Option A)))≤
      2*(Fintype.card E:ℚ)*Δ := by
  let f : Sample R C A→ℚ := fun z => J1MainSourceCollision.deviation (edgeCell row col z)
  let w := marginal (fun _ : R⊕C => (none : Option A))
  have H : GuardExpectation.average w (fun z => f (splitSample z)) = compressed row col w :=
    compressed_correct row col w (marginal_normalized _)
  change compressed row col w≤_
  rw [← H]
  change GuardExpectation.average (fun _ : R⊕C => fun _ : A => (Fintype.card A:ℚ)⁻¹)
    (fun z => f (splitSample z))≤_
  rw [uniform_product_mean,mean_equiv splitSample f]
  exact expected_squared_loads row col Δ hr hc

private theorem length_of_menu {I : Type*} [Fintype I] (xs : List I) (hn : xs.Nodup)
    (hA : ∀ i : I, i ∈ xs) : xs.length=Fintype.card I := by
  rw [← List.toFinset_card_of_nodup hn]
  have hh : xs.toFinset=Finset.univ := by ext i; simp [hA i]
  rw [hh,Finset.card_univ]

/-- Pattern actual source calls: finite indexed graph, each vertex and
label word enumerated once. This proves the final assignment and the
bit-step cost of the whole conditional-expectation selection phase. -/
theorem complete_greedy (F : Format E R C A) (first : A) (rest : List A) (vs : List (R⊕C))
    (hvs : vs.Nodup) (hVertices : ∀ i : R⊕C, i ∈ vs)
    (hNoLabels : (first::rest).Nodup) (hLabels : ∀ a : A, a ∈ first::rest)
    (Δ : ℕ) (hr : ∀ v, (fibre F.row v).card≤Δ) (hc : ∀ v, (fibre F.col v).card≤Δ) :
    let G := run F.width F.kR F.kC F.b F.literals (F.label first) (rest.map F.label)
      (vs.map F.target) (F.graph (fun _ => none))
    ∃ z : R⊕C→A,
      G.result.1=F.graph (fun i => some (z i)) ∧
      G.result.2=vs.map (fun i => F.label (z i)) ∧
      J1MainSourceCollision.deviation (edgeCell F.row F.col (splitSample z))≤
        2*(Fintype.card E:ℚ)*Δ ∧
      G.steps≤(F.stepBound (Fintype.card A)+2*F.b+6)*(Fintype.card R+Fintype.card C) := by
  let p₀ : R⊕C→Option A := fun _ => none
  let prev := spec F first rest vs p₀
  obtain ⟨hrun,htrace,hcost⟩ := run_exact F first rest vs p₀
  have H (i : R⊕C) : ∃ a, prev.1 i=some a := spec_total_on_schedule F first rest vs p₀ i (hVertices i)
  let z (i : R⊕C) : A := Classical.choose (H i)
  have hp : prev.1=(fun i => some (z i)) := funext fun i => Classical.choose_spec (H i)
  have hm := spec_nonincreasing F first rest vs p₀ hLabels
  have hv := (compare_candidates F.row F.col prev.1 p₀).mp hm
  have hvar : J1MainSourceCollision.deviation (edgeCell F.row F.col (splitSample z))≤
      2*(Fintype.card E:ℚ)*Δ := by
    rw [hp,compressed_full] at hv
    exact hv.trans (compressed_initial F.row F.col Δ hr hc)
  have hl : prev.2.map some = vs.map prev.1 := spec_trace F first rest vs p₀ hvs
  have ht : prev.2=vs.map z := by
    rw [hp] at hl
    have he := congrArg (List.map (fun t : Option A => t.getD first)) hl
    simp only [List.map_map] at he
    change prev.2.map id=vs.map z at he
    simpa only [List.map_id] using he
  have hnl : rest.length+1=Fintype.card A := length_of_menu (first::rest) hNoLabels hLabels
  have hnv : vs.length=Fintype.card R+Fintype.card C :=
    (length_of_menu vs hvs hVertices).trans Fintype.card_sum
  refine ⟨z,?_,?_,hvar,?_⟩
  · exact hrun.trans (congrArg F.graph hp)
  · rw [htrace,ht,List.map_map]
    rfl
  · simpa only [hnl,hnv] using hcost

#print axioms run_exact
#print axioms spec_total_on_schedule
#print axioms spec_trace
#print axioms spec_nonincreasing
#print axioms compressed_full
#print axioms compressed_initial
#print axioms complete_greedy

end J6R12CollisionRun
