import P5FrontendG1ExistencePrinted

/-! A concrete terminating exhaustive reference search over the actual
binary tuple/matrix charts and finite checkers. The list semantics is
not a proof of the source's streamed space or bit-time bounds. -/
namespace Paper5.FrontendG1.Tanner

def allTuples {A : Type*} (L : List A) : (n : ℕ)→List (Fin n→A)
  | 0 => [Fin.elim0]
  | n+1 => L.flatMap fun a => (allTuples L n).map (Fin.cons a)

theorem allTuples_complete {A : Type*} (L : List A) (hL : ∀ a : A,a∈L) :
    ∀ (n : ℕ) (f : Fin n→A),f∈allTuples L n := by
  intro n
  induction n with
  | zero =>
    intro f
    rw [allTuples,List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro f
    simp only [allTuples,List.mem_flatMap,List.mem_map]
    exact ⟨f 0,hL _,Fin.tail f,ih _,Fin.cons_self_tail f⟩

theorem allTuples_length {A : Type*} (L : List A) : ∀ n, (allTuples L n).length=L.length^n := by
  intro n
  induction n with
  | zero => simp [allTuples]
  | succ n ih =>
    simp [allTuples,List.length_flatMap,ih,pow_succ']

def alphabet : List F₂ := [0,1]

theorem alphabet_complete (a : F₂) : a∈alphabet := by
  rcases binary_cases a with rfl|rfl <;> simp [alphabet]

def shiftCandidates (B m : ℕ) : List (SourceShifts B m) :=
  allTuples (allTuples alphabet (sourceEll B m)) (sourceDegree B m)

def localCandidates (B m : ℕ) :
    List (Matrix (Fin (sourceLocalRows B m)) (Fin (sourceDegree B m)) F₂) :=
  allTuples (allTuples alphabet (sourceDegree B m)) (sourceLocalRows B m)

theorem shift_candidates_complete {B m : ℕ} (s : SourceShifts B m) :
    s∈shiftCandidates B m :=
  allTuples_complete _ (allTuples_complete alphabet alphabet_complete _) _ s

theorem local_candidates_complete {B m : ℕ}
    (A : Matrix (Fin (sourceLocalRows B m)) (Fin (sourceDegree B m)) F₂) :
    A∈localCandidates B m :=
  allTuples_complete _ (allTuples_complete alphabet alphabet_complete _) _ A

theorem source_search_lengths (B m : ℕ) :
    (shiftCandidates B m).length=2^(sourceEll B m*sourceDegree B m) ∧
    (localCandidates B m).length=2^(sourceDegree B m*sourceLocalRows B m) := by
  constructor
  · change (allTuples (allTuples alphabet (sourceEll B m)) (sourceDegree B m)).length=_
    rw [allTuples_length,allTuples_length,pow_mul]
    rfl
  · change (allTuples (allTuples alphabet (sourceDegree B m)) (sourceLocalRows B m)).length=_
    rw [allTuples_length,allTuples_length,pow_mul]
    rfl

def firstShift (B m : ℕ) : Option (SourceShifts B m) :=
  (shiftCandidates B m).find? fun s=>decide (biasViolations B m s=∅)

def firstLocal (B m : ℕ) :
    Option (Matrix (Fin (sourceLocalRows B m)) (Fin (sourceDegree B m)) F₂) :=
  (localCandidates B m).find? fun A=>decide (localViolations A (sourceMinDistance B m)=∅)

private theorem find_checked {X : Type*} (L : List X) (p : X→Bool)
    (h : ∃ x∈L,p x=true) : ∃ x,L.find? p=some x ∧ p x=true := by
  cases hF : L.find? p with
  | none =>
    obtain ⟨x,hx,hp⟩ := h
    exact ((List.find?_eq_none.mp hF) x hx hp).elim
  | some x => exact ⟨x,rfl,List.find?_some hF⟩

theorem first_shift_returns_valid {B m : ℕ} (hB : 0<B) (hm : 0<m) :
    ∃ s,firstShift B m=some s ∧ biasViolations B m s=∅ := by
  obtain ⟨s,hs⟩ := source_valid_shift_tuple_exists hB hm
  obtain ⟨v,hV,hPass⟩ := find_checked (shiftCandidates B m)
    (fun a=>decide (biasViolations B m a=∅))
    ⟨s,shift_candidates_complete s,decide_eq_true hs⟩
  exact ⟨v,hV,of_decide_eq_true hPass⟩

theorem first_local_returns_valid {B m : ℕ} (hB : 0<B) (hm : 0<m) :
    ∃ A,firstLocal B m=some A ∧ localViolations A (sourceMinDistance B m)=∅ := by
  obtain ⟨A,hA⟩ := source_local_matrix_exists hB hm
  obtain ⟨v,hV,hPass⟩ := find_checked (localCandidates B m)
    (fun a=>decide (localViolations a (sourceMinDistance B m)=∅))
    ⟨A,local_candidates_complete A,decide_eq_true hA⟩
  exact ⟨v,hV,of_decide_eq_true hPass⟩

theorem first_search_has_printed_input {C : Type*} [Fintype C] {B : ℕ}
    (hB : 0<B) (hm : 0<Fintype.card C) :
    ∃ P : PrintedInput C B,
      firstShift B (Fintype.card C)=some P.shifts ∧
      firstLocal B (Fintype.card C)=some P.checks ∧
      SourceBias B (Fintype.card C) P.shifts := by
  obtain ⟨s,hs,hb⟩ := first_shift_returns_valid hB hm
  obtain ⟨A,hA,hc⟩ := first_local_returns_valid hB hm
  obtain ⟨keep⟩ := printed_kept_columns_exist C B hB hm
  exact ⟨checkedInput s A keep hc,hs,hA,(biasViolations_empty_exact hB s).mp hb⟩

#print axioms allTuples_complete
#print axioms allTuples_length
#print axioms alphabet_complete
#print axioms shift_candidates_complete
#print axioms local_candidates_complete
#print axioms source_search_lengths
#print axioms first_shift_returns_valid
#print axioms first_local_returns_valid
#print axioms first_search_has_printed_input
end Paper5.FrontendG1.Tanner