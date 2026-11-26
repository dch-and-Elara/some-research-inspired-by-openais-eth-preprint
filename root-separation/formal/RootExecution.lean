import RootProgram
import S11TraceCore
import Mathlib.Data.ZMod.Basic

namespace RootSeparation.Execution

open S11

/-- One ripple-carry transition on the tracked coefficient coordinate. -/
structure Digit where
  slot : Slot
  index : ℕ
  left : ℕ
  right : ℕ
  carryIn : Bool
  output : ℕ
  carryOut : Bool

/-- The two observations of the root body: a child return used in its
product, and an executed digit transition. -/
inductive Step
  | childReturn (slot : Slot) (group : Fin 64)
  | digit (update : Digit)

def Step.asDigit : Step → Option Digit
  | .digit d => some d
  | .childReturn _ _ => none

def Digit.firstSlot (d : Digit) : Option Slot :=
  if d.index = 0 then some d.slot else none

def executedDigits (trace : List Step) : List Digit := trace.filterMap Step.asDigit

def rootProjection (trace : List Step) : List Slot :=
  (executedDigits trace).filterMap Digit.firstSlot

/-- Track the executed bit additions, sharing the state update of addWord.
The high part sees the new carry and the remaining high operand words. -/
def addTracked (slot : Slot) : ℕ → ℕ → ℕ → ℕ → Bool → ℕ × List Digit
  | 0, _, _, _, _ => (0, [])
  | p+1, i, x, y, cin =>
    let left := x % 2
    let right := y % 2
    let digit := left + right + cin.toNat
    let cout := decide (2 ≤ digit)
    let rest := addTracked slot p (i+1) (x/2) (y/2) cout
    ((digit % 2) + 2*rest.1, ⟨slot,i,left,right,cin,digit%2,cout⟩ :: rest.2)

theorem addTracked_value (slot : Slot) (p i x y : ℕ) (cin : Bool) :
    (addTracked slot p i x y cin).1 = (addWord p x y cin).1 := by
  induction p generalizing i x y cin with
  | zero => rfl
  | succ p ih => simp [addTracked, addWord, ih]

theorem addTracked_length (slot : Slot) (p i x y : ℕ) (cin : Bool) :
    (addTracked slot p i x y cin).2.length = p := by
  induction p generalizing i x y cin with
  | zero => rfl
  | succ p ih => simp [addTracked, ih]

private theorem addTracked_noFirst (slot : Slot) (p i x y : ℕ) (cin : Bool) (hi : 0 < i) :
    (addTracked slot p i x y cin).2.filterMap Digit.firstSlot = [] := by
  induction p generalizing i x y cin with
  | zero => rfl
  | succ p ih => simp [addTracked, Digit.firstSlot, Nat.ne_of_gt hi, ih]

theorem addTracked_first (slot : Slot) (p x y : ℕ) (cin : Bool) (hp : 0 < p) :
    (addTracked slot p 0 x y cin).2.filterMap Digit.firstSlot = [slot] := by
  cases p with
  | zero => omega
  | succ p => simp [addTracked, Digit.firstSlot, addTracked_noFirst]

/-- Modular coordinates for the additive representation specified in
contraction:40–47. A codec is a representation interface for the ring
passed to the loop. Multiplication takes place in that ring. -/
abbrev Coords (I : Type*) (p : ℕ) := I → ZMod (2^p)

structure BatchState (I : Type*) (p : ℕ) where
  accumulator : Coords I p
  reversed : List Step

def BatchState.trace (st : BatchState I p) : List Step := st.reversed.reverse

def groupProduct {R : Type*} [CommSemiring R] (slot : Slot)
    (child : Slot → Fin 64 → R) (groups : List (Fin 64)) : R × List Step :=
  groups.foldl (fun st g => (st.1 * child slot g, .childReturn slot g :: st.2)) (1,[])

private theorem groupProduct_value {R : Type*} [CommSemiring R] (slot : Slot)
    (child : Slot → Fin 64 → R) (groups : List (Fin 64)) :
    (groupProduct slot child groups).1 = (groups.map (child slot)).prod := by
  have fold (gs : List (Fin 64)) (st : R × List Step) :
      (gs.foldl (fun st g => (st.1 * child slot g, Step.childReturn slot g :: st.2)) st).1 =
        st.1 * (gs.map (child slot)).prod := by
    induction gs generalizing st with
    | nil => simp
    | cons g gs ih => simp [List.foldl_cons, ih, mul_assoc]
  simpa [groupProduct] using fold groups (1,[])

theorem groupProduct_order {R : Type*} [CommSemiring R] (slot : Slot)
    (child : Slot → Fin 64 → R) (groups : List (Fin 64)) :
    (groupProduct slot child groups).2.reverse = groups.map (Step.childReturn slot) := by
  have fold (gs : List (Fin 64)) (st : R × List Step) :
      (gs.foldl (fun st g => (st.1 * child slot g, Step.childReturn slot g :: st.2)) st).2.reverse =
        st.2.reverse ++ gs.map (Step.childReturn slot) := by
    induction gs generalizing st with
    | nil => simp
    | cons g gs ih => simp [List.foldl_cons, ih, List.reverse_cons, List.append_assoc]
  simpa [groupProduct] using fold groups (1,[])

private theorem groupProduct_noDigits {R : Type*} [CommSemiring R] (slot : Slot)
    (child : Slot → Fin 64 → R) (groups : List (Fin 64)) :
    executedDigits (groupProduct slot child groups).2.reverse = [] := by
  rw [groupProduct_order]
  simp [executedDigits, List.filterMap_map, Function.comp_def, Step.asDigit]

def stepTuple {R I : Type*} [CommSemiring R] [DecidableEq I] {p : ℕ}
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → R)
    (st : BatchState I p) (slot : Slot) : BatchState I p :=
  let prod := groupProduct slot child (List.finRange 64)
  let term := codec prod.1
  let add := addTracked slot p 0 (st.accumulator track).val (term track).val false
  let sum : Coords I p := fun i =>
    if i = track then (add.1 : ZMod (2^p))
    else ((addWord p (st.accumulator i).val (term i).val false).1 : ZMod (2^p))
  ⟨sum, (add.2.reverse.map Step.digit) ++ prod.2 ++ st.reversed⟩

private theorem modularWord (p : ℕ) (x y : ZMod (2^p)) :
    ((addWord p x.val y.val false).1 : ZMod (2^p)) = x+y := by
  haveI : NeZero (2^p) := ⟨by positivity⟩
  rw [addWord_value]
  simp [ZMod.natCast_mod]

theorem stepTuple_value {R I : Type*} [CommSemiring R] [DecidableEq I] {p : ℕ}
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → R)
    (st : BatchState I p) (slot : Slot) :
    codec.symm (stepTuple codec track child st slot).accumulator =
      codec.symm st.accumulator + ((List.finRange 64).map (child slot)).prod := by
  apply codec.injective
  simp only [AddEquiv.apply_symm_apply, map_add]
  funext i
  simp only [stepTuple, Pi.add_apply, addTracked_value, groupProduct_value]
  split
  · next hi => subst i; exact modularWord p _ _
  · exact modularWord p _ _

theorem stepTuple_project {R I : Type*} [CommSemiring R] [DecidableEq I] {p : ℕ}
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → R)
    (st : BatchState I p) (slot : Slot) (hp : 0 < p) :
    rootProjection (stepTuple codec track child st slot).trace = rootProjection st.trace ++ [slot] := by
  simp [stepTuple, BatchState.trace, rootProjection, executedDigits, List.filterMap_map,
    Function.comp_def, Step.asDigit, addTracked_first, hp,
    show ((groupProduct slot child (List.finRange 64)).2.reverse.filterMap Step.asDigit) = [] from
      groupProduct_noDigits _ _ _]

theorem stepTuple_digits {R I : Type*} [CommSemiring R] [DecidableEq I] {p : ℕ}
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → R)
    (st : BatchState I p) (slot : Slot) :
    (executedDigits (stepTuple codec track child st slot).trace).length =
      (executedDigits st.trace).length + p := by
  simp [stepTuple, BatchState.trace, executedDigits, List.filterMap_map,
    Function.comp_def, Step.asDigit, addTracked_length,
    show ((groupProduct slot child (List.finRange 64)).2.reverse.filterMap Step.asDigit) = [] from
      groupProduct_noDigits _ _ _]

/-- The remaining-budget iterator calls the actual state update at each
leaf. The implementation consumes weights and budget, not a list of slots. -/
def executeBatch {R I : Type*} [CommSemiring R] [DecidableEq I] (p : ℕ)
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → R)
    (ws : List ℕ) (t : ℤ) (j : ℕ) : BatchState I p :=
  foldTuples ws p (fun st β => stepTuple codec track child st ⟨t,j,β⟩) ⟨0,[]⟩

theorem executeBatch_project {R I : Type*} [CommSemiring R] [DecidableEq I] (p : ℕ)
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → R)
    (ws : List ℕ) (t : ℤ) (j : ℕ) (hp : 0 < p) :
    rootProjection (executeBatch p codec track child ws t j).trace =
      (tuples ws p).map (Slot.mk t j) := by
  have fold (l : List (List ℕ)) (st : BatchState I p) :
      rootProjection (l.foldl (fun a β => stepTuple codec track child a ⟨t,j,β⟩) st).trace =
      rootProjection st.trace ++ l.map (Slot.mk t j) := by
    induction l generalizing st with
    | nil => simp
    | cons β l ih =>
      simp only [List.foldl_cons, ih, stepTuple_project _ _ _ _ _ hp, List.map_cons,
        List.append_assoc, List.singleton_append]
  unfold executeBatch
  rw [foldTuples_eq, fold]
  rfl

theorem executeBatch_digits {R I : Type*} [CommSemiring R] [DecidableEq I] (p : ℕ)
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → R)
    (ws : List ℕ) (t : ℤ) (j : ℕ) :
    (executedDigits (executeBatch p codec track child ws t j).trace).length =
      (tuples ws p).length * p := by
  have fold (l : List (List ℕ)) (st : BatchState I p) :
      (executedDigits (l.foldl (fun a β => stepTuple codec track child a ⟨t,j,β⟩) st).trace).length =
        (executedDigits st.trace).length + l.length * p := by
    induction l generalizing st with
    | nil => simp
    | cons β l ih =>
      simp only [List.foldl_cons, ih, stepTuple_digits, List.length_cons, Nat.succ_mul]
      omega
  unfold executeBatch
  rw [foldTuples_eq, fold]
  simp [BatchState.trace, executedDigits]

theorem executeBatch_value {R I : Type*} [CommSemiring R] [DecidableEq I] (p : ℕ)
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → R)
    (ws : List ℕ) (t : ℤ) (j : ℕ) :
    codec.symm (executeBatch p codec track child ws t j).accumulator =
      (((tuples ws p).map fun β => ((List.finRange 64).map (child ⟨t,j,β⟩)).prod)).sum := by
  have fold (l : List (List ℕ)) (st : BatchState I p) :
      codec.symm (l.foldl (fun a β => stepTuple codec track child a ⟨t,j,β⟩) st).accumulator =
        codec.symm st.accumulator +
          (l.map fun β => ((List.finRange 64).map (child ⟨t,j,β⟩)).prod).sum := by
    induction l generalizing st with
    | nil => simp
    | cons β l ih => simp [List.foldl_cons, ih, stepTuple_value, add_assoc]
  simp [executeBatch, foldTuples_eq, fold]

theorem filterMap_ordered {α β : Type*} (f : α → Option β) (l : List α) :
    ∃ e : Fin (l.filterMap f).length → Fin l.length, StrictMono e ∧
      ∀ i, f (l.get (e i)) = some ((l.filterMap f).get i) := by
  induction l with
  | nil => exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | cons a l ih =>
    obtain ⟨e,he,hget⟩ := ih
    cases h : f a with
    | none =>
      rw [List.filterMap_cons_none h]
      simp only [List.length_cons]
      exact ⟨fun i => (e i).succ, fun i j hij => Fin.succ_lt_succ_iff.mpr (he hij),
        fun i => hget i⟩
    | some b =>
      rw [List.filterMap_cons_some h]
      simp only [List.length_cons]
      let go : Fin ((l.filterMap f).length + 1) → Fin (l.length + 1) :=
        Fin.cases 0 (fun i => (e i).succ)
      refine ⟨go, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · intro j
          refine Fin.cases ?_ (fun j' => ?_) j
          · simp
          · simp [go]
        · intro j
          refine Fin.cases ?_ (fun j' => ?_) j
          · simp
          · simp only [go, Fin.cases_succ, Fin.succ_lt_succ_iff]
            exact fun hij => he hij
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · exact h
        · exact hget i'

theorem projection_ordered_injection (trace : List Step) :
    ∃ e : Fin (rootProjection trace).length → Fin (executedDigits trace).length,
      StrictMono e ∧ ∀ i, ((executedDigits trace).get (e i)).firstSlot =
        some ((rootProjection trace).get i) :=
  filterMap_ordered Digit.firstSlot (executedDigits trace)

#print axioms projection_ordered_injection
#print axioms addTracked_value
#print axioms addTracked_first
#print axioms stepTuple_value
#print axioms groupProduct_order
#print axioms stepTuple_digits
#print axioms executeBatch_project
#print axioms executeBatch_digits
#print axioms executeBatch_value

end RootSeparation.Execution
