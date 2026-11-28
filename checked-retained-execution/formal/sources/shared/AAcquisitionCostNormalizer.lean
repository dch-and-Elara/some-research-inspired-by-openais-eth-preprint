import AAcquisitionCostSeats

/-! A4's public nuisance factors from a serial scan of explicit address
records. The fixed-width encoding here is deliberately unary/one-hot;
there is no cost-free multiword comparison or machine-index lookup.
Multiplying the factors and final integer division are separate below.
-/

namespace AAcquisitionCost
open scoped BigOperators

def oneHot {c : ℕ} (i : Fin c) : List Bool :=
  List.ofFn fun j : Fin c => decide (j = i)

theorem oneHot_get {c : ℕ} (i j : Fin c) :
    (oneHot i)[j.val]? = some (decide (j=i)) := by
  simp [oneHot,j.isLt]

theorem oneHot_injective (c : ℕ) : Function.Injective (@oneHot c) := by
  intro i j h
  have e := congrArg (fun xs : List Bool => xs[i.val]?) h
  change (oneHot i)[i.val]? = (oneHot j)[i.val]? at e
  rw [oneHot_get i i,oneHot_get j i] at e
  simpa using e

/-- Three fixed bit operations (read/read/compare) and one AND at each
paired symbol, plus a single end test. No short-circuit consumption is
used, so the trace price is independent of whether the words match. -/
def compareWord : List Bool → List Bool → Bool × ℕ
  | [], [] => (true,1)
  | x::xs, y::ys =>
    let r := compareWord xs ys
    ((x == y) && r.1, r.2+4)
  | _, _ => (false,1)

theorem compareWord_exact (xs ys : List Bool) :
    (compareWord xs ys).1 = decide (xs=ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [compareWord]
  | cons x xs ih =>
    cases ys with
    | nil => simp [compareWord]
    | cons y ys => cases x <;> cases y <;> simp [compareWord, ih]

theorem compareWord_budget (xs ys : List Bool) :
    (compareWord xs ys).2 ≤ 4*xs.length+1 := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [compareWord]
  | cons x xs ih =>
    cases ys with
    | nil => simp [compareWord]
    | cons y ys =>
      have h := ih ys
      simp only [compareWord,List.length_cons,Nat.mul_succ]
      omega

/-- The A4 load cap is tested by a fixed 3-state transition, after the
tag/read/compare. In the valid layout it never drops a true hit. -/
def countRecord (target : List Bool) : List (Option (List Bool)) → ℕ × ℕ
  | [] => (0,0)
  | none::xs =>
    let r := countRecord target xs
    (r.1,r.2+1)
  | some row::xs =>
    let z := compareWord row target
    let r := countRecord target xs
    (min 2 (r.1+if z.1 then 1 else 0), r.2+z.2+8)

theorem countRecord_exact (target : List Bool) (rows : List (Option (List Bool))) :
    (countRecord target rows).1 = min 2 (rows.countP fun w => decide (w=some target)) := by
  induction rows with
  | nil => simp [countRecord]
  | cons row rows ih =>
    cases row with
    | none => simpa [countRecord] using ih
    | some row =>
      simp only [countRecord, compareWord_exact, List.countP_cons, Option.some.injEq, ih]
      by_cases h : row = target <;> simp [h]
      all_goals omega

theorem countRecord_budget (target : List Bool) (rows : List (Option (List Bool)))
    (width : ℕ) (valid : ∀ w, some w ∈ rows → w.length ≤ width) :
    (countRecord target rows).2 ≤ (4*width+9)*rows.length := by
  induction rows with
  | nil => simp [countRecord]
  | cons row rows ih =>
    have hr := ih (fun w h => valid w (List.mem_cons_of_mem _ h))
    cases row with
    | none => simp only [countRecord,List.length_cons,Nat.mul_succ]; omega
    | some row =>
      have h := (compareWord_budget row target).trans (by
        have hl := valid row (by simp)
        omega : 4*row.length+1 ≤ 4*width+1)
      simp only [countRecord,List.length_cons,Nat.mul_succ]
      omega

def tapTape {u c : ℕ} (tap : Fin u → Option (Fin c)) : List (Option (List Bool)) :=
  (List.finRange u).map (fun i => (tap i).map oneHot)

theorem tapTape_hits {u c : ℕ} (tap : Fin u → Option (Fin c)) (a : Fin c) :
    (countRecord (oneHot a) (tapTape tap)).1 = min 2 (Acquisition.unaryLoad tap a) := by
  rw [countRecord_exact,tapTape,List.countP_map]
  have mapEq (i : Fin u) :
      ((tap i).map oneHot = some (oneHot a)) ↔ tap i = some a := by
    cases h : tap i with
    | none => simp
    | some b => simp only [Option.map_some,Option.some.injEq]; exact (oneHot_injective c).eq_iff
  simp only [Function.comp_def,mapEq]
  rw [Acquisition.unaryLoad,Fintype.card_subtype,List.countP_eq_length_filter,Fin.univ_def]
  rfl

theorem tapTape_budget {u c : ℕ} (tap : Fin u → Option (Fin c)) (a : Fin c) :
    (countRecord (oneHot a) (tapTape tap)).2 ≤ (4*c+9)*u := by
  have h : (tapTape tap).length = u := by simp [tapTape]
  have hwidth : ∀ w, some w ∈ tapTape tap → w.length ≤ c := by
    intro w hw
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hw
    cases hh : tap j with
    | none => simp [hh] at he
    | some b =>
      have e : oneHot b = w := by simpa [hh] using he
      simp [← e,oneHot]
  simpa only [h] using countRecord_budget (oneHot a) (tapTape tap) c hwidth

def factorTape {u c : ℕ} (tap : Fin u → Option (Fin c)) : List ℕ :=
  (List.finRange c).map fun a => 1+2^(countRecord (oneHot a) (tapTape tap)).1

theorem factorTape_exact {u c : ℕ} (tap : Fin u → Option (Fin c))
    (cap : ∀ a, Acquisition.unaryLoad tap a ≤ 2) :
    (factorTape tap).prod = Acquisition.publicFactor tap := by
  unfold factorTape Acquisition.publicFactor
  simp_rw [tapTape_hits, min_eq_right (cap _)]
  rw [Fin.univ_def,Finset.prod_mk]
  rfl

def factorScanCost {u c : ℕ} (tap : Fin u → Option (Fin c)) : ℕ :=
  ((List.finRange c).map fun a => (countRecord (oneHot a) (tapTape tap)).2).sum

theorem factorScanCost_budget {u c : ℕ} (tap : Fin u → Option (Fin c)) :
    factorScanCost tap ≤ c*((4*c+9)*u) := by
  unfold factorScanCost
  have h (xs : List (Fin c)) :
      (xs.map fun a => (countRecord (oneHot a) (tapTape tap)).2).sum ≤
        xs.length*((4*c+9)*u) := by
    induction xs with
    | nil => simp
    | cons a as ih =>
      simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm]
        using Nat.add_le_add (tapTape_budget tap a) ih
  simpa using h (List.finRange c)

#print axioms compareWord_exact
#print axioms compareWord_budget
#print axioms countRecord_exact
#print axioms countRecord_budget
#print axioms tapTape_hits
#print axioms tapTape_budget
#print axioms factorTape_exact
#print axioms factorScanCost_budget

end AAcquisitionCost
