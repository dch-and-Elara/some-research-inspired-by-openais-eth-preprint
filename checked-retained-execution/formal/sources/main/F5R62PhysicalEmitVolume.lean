import F5R62PhysicalEmit

/-! Count the real emitted list, including the actual sum of generated
cycle lengths, not the independent index-size proxy of R60. -/
namespace F5R62.PhysicalEmit
set_option autoImplicit false
set_option warningAsError true
open F5R60 F5R61

def literalCount {V E T : Type} (F : CNF V E T) : ℕ :=
  (F.map List.length).sum

theorem literal_count_append {V E T : Type} (X Y : CNF V E T) :
    literalCount (X++Y)=literalCount X+literalCount Y := by
  simp only [literalCount,List.map_append,List.sum_append_nat]

private theorem literal_count_flatMap {I V E T : Type} (xs : List I) (f : I → CNF V E T) :
    literalCount (xs.flatMap f)=(xs.map (fun x => literalCount (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons,literal_count_append,ih,List.map_cons,List.sum_cons]

private theorem literal_count_map {I V E T : Type} (xs : List I) (f : I → Row V E T) :
    literalCount (xs.map f)=(xs.map (fun x => (f x).length)).sum := by
  rw [literalCount,List.map_map]
  rfl

private theorem nat_sum_map_constant {I : Type} (l : List I) (c : ℕ) :
    (l.map (fun _ => c)).sum = c*l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.mul_succ]
    omega

private theorem nat_sum_map_add {I : Type} (l : List I) (f g : I → ℕ) :
    (l.map (fun x => f x+g x)).sum=(l.map f).sum+(l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    omega

private theorem nat_sum_map_double {I : Type} (l : List I) (f : I → ℕ) :
    (l.map (fun x => 2*f x)).sum=2*(l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    omega

private theorem one_indicator {I : Type} [DecidableEq I] (q : I) (xs : List I) (nd : xs.Nodup) :
    (xs.map (fun y => if q=y then (1:ℕ) else 0)).sum=if q∈xs then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hn := List.nodup_cons.mp nd
    rw [List.map_cons,List.sum_cons,ih hn.2]
    by_cases e : q=x
    · subst q
      simp [hn.1]
    · by_cases h : q∈xs
      · simp [e,h]
      · simp [e,h]

private theorem filter_head_count {A I : Type} [DecidableEq I]
    (key : A → I) (x : A) (xs : List A) (q : I) :
    ((x::xs).filter (fun y => decide (key y=q))).length=
      (if key x=q then 1 else 0)+(xs.filter (fun y => decide (key y=q))).length := by
  by_cases h : key x=q
  · simp [h]
    omega
  · simp [h]

private theorem partition_lengths {A I : Type} [DecidableEq I]
    (L : Listing I) (key : A → I) (xs : List A) :
    (L.elems.map (fun q => (xs.filter (fun y => decide (key y=q))).length)).sum=xs.length := by
  induction xs with
  | nil =>
    have h := nat_sum_map_constant L.elems 0
    simpa only [List.filter_nil,List.length_nil,Nat.zero_mul] using h
  | cons x xs ih =>
    simp_rw [filter_head_count, nat_sum_map_add]
    rw [one_indicator _ _ L.once, if_pos (L.all (key x)), ih]
    simp only [List.length_cons]
    omega

variable {V E T : Type}

def copyBudget (v : Listing V) (e : Listing E) (t : Listing T) : ℕ :=
  2*v.elems.length+5*e.elems.length+10*t.elems.length

theorem base_row_count (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T) :
    (baseRows G v e t).length=v.elems.length+2*e.elems.length+4*t.elems.length := by
  simp only [baseRows,List.length_append,List.length_map,List.length_flatMap]
  change v.elems.length+((e.elems.map (fun _ => (2:ℕ))).sum+(t.elems.map (fun _ => (4:ℕ))).sum)=_
  rw [nat_sum_map_constant,nat_sum_map_constant]
  omega

theorem base_literal_count (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T) :
    literalCount (baseRows G v e t)=copyBudget v e t := by
  rw [baseRows,literal_count_append,literal_count_append,literal_count_map,
    literal_count_flatMap,literal_count_flatMap]
  change (v.elems.map (fun _ => (2:ℕ))).sum+
    ((e.elems.map (fun _ => (5:ℕ))).sum+(t.elems.map (fun _ => (10:ℕ))).sum)=_
  rw [nat_sum_map_constant,nat_sum_map_constant,nat_sum_map_constant]
  unfold copyBudget
  omega

private theorem forbidden_length (v : Listing V) (e : Listing E) (t : Listing T) :
    (allForbidden v e t).length=v.elems.length+e.elems.length+t.elems.length := by
  simp [allForbidden,switches,directedRequests,tripleRequests,Nat.add_assoc]

private theorem spare_length (e : Listing E) (t : Listing T) :
    (allSingles (V:=V) e t).length=3*e.elems.length+8*t.elems.length := by
  rw [allSingles,List.length_append,List.length_flatMap,List.length_flatMap]
  change (e.elems.map (fun _ => (3:ℕ))).sum+(t.elems.map (fun _ => (8:ℕ))).sum=_
  rw [nat_sum_map_constant,nat_sum_map_constant]

private theorem chain_length (p : PrivatePos V E T) (xs : List (PrivatePos V E T)) :
    (chainRows p xs).length=xs.length := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp [chainRows,ih]

private theorem chain_mass (p : PrivatePos V E T) (xs : List (PrivatePos V E T)) :
    literalCount (chainRows p xs)=2*xs.length := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    change 2+literalCount (chainRows x xs)=2*(xs.length+1)
    rw [ih]
    omega

theorem one_cycle_row_count {G : RequestGraph V E T} (D : PrintedCycles G) (n : Logical V T) :
    (cycleRowsAt D n).length=(D.rest n).length+1 := by
  simp [cycleRowsAt,chain_length]

theorem one_cycle_literal_count {G : RequestGraph V E T} (D : PrintedCycles G) (n : Logical V T) :
    literalCount (cycleRowsAt D n)=2*((D.rest n).length+1) := by
  rw [cycleRowsAt,literal_count_append,chain_mass]
  change 2*(D.rest n).length+2=2*((D.rest n).length+1)
  omega

variable [DecidableEq V] [DecidableEq T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

theorem one_generated_cycle_row_count (n : Logical V T) :
    ((generatedPrintedCycles G v e t).rest n).length+1=
      2*(pairsOf G v e t n).length+(singlesOf G e t n).length := by
  have r := congrArg List.length (reconstruct_cycle_list G v e t n)
  change ((generatedPrintedCycles G v e t).rest n).length+1=(actualCycleList G v e t n).length at r
  exact r.trans (orderedSlots_size (pairsOf G v e t n) (singlesOf G e t n))

private theorem generated_counts_sum :
    ((logicalListing v t).elems.map (fun n=>((generatedPrintedCycles G v e t).rest n).length+1)).sum=
      copyBudget v e t := by
  have pairs := partition_lengths (logicalListing v t)
    (fun p : PrivatePos V E T × PrivatePos V E T => nameOf G p.1) (allForbidden v e t)
  have singles := partition_lengths (logicalListing v t) (nameOf G) (allSingles (V:=V) e t)
  simp_rw [one_generated_cycle_row_count, nat_sum_map_add, nat_sum_map_double]
  unfold pairsOf singlesOf
  rw [pairs,singles,forbidden_length,spare_length]
  unfold copyBudget
  omega

theorem actual_generated_cycle_counts :
    let D := generatedPrintedCycles G v e t
    (cycleRows D v t).length=copyBudget v e t ∧
      literalCount (cycleRows D v t)=2*copyBudget v e t := by
  dsimp only
  constructor
  · rw [cycleRows,List.length_flatMap]
    simpa only [one_cycle_row_count] using generated_counts_sum G v e t
  · rw [cycleRows,literal_count_flatMap]
    simp only [one_cycle_literal_count,nat_sum_map_double,generated_counts_sum]

theorem exact_f1_emitted_list_volume :
    let K := copyBudget v e t
    let F := f1ActualCNF G v e t
    F.length=v.elems.length+2*e.elems.length+4*t.elems.length+K+1 ∧
      literalCount F=3*K+2 := by
  dsimp only
  obtain ⟨c₁,c₂⟩ := actual_generated_cycle_counts G v e t
  constructor
  · rw [f1ActualCNF,List.length_append,List.length_append,base_row_count,c₁]
    change _ + (copyBudget v e t + 1) = _
    omega
  · rw [f1ActualCNF,literal_count_append,literal_count_append,base_literal_count,c₂]
    change copyBudget v e t+(2*copyBudget v e t+2)=3*copyBudget v e t+2
    omega

private theorem listing_card_exact {I : Type} [Fintype I] (L : Listing I) :
    L.elems.length=Fintype.card I := by
  classical
  have h : L.elems.toFinset = Finset.univ := by
    ext i
    simp [L.all i]
  rw [← List.toFinset_card_of_nodup L.once,h,Finset.card_univ]

theorem exact_f1_emitted_list_at_printed_sizes [Fintype V] [Fintype E] [Fintype T] :
    let F := f1ActualCNF G v e t
    F.length=Fintype.card V+2*Fintype.card E+4*Fintype.card T+printedK V E T+1 ∧
      literalCount F=3*printedK V E T+2 := by
  have h := exact_f1_emitted_list_volume G v e t
  dsimp only at h ⊢
  simpa only [copyBudget,listing_card_exact,printedK] using h

#print axioms literal_count_append
#print axioms base_row_count
#print axioms base_literal_count
#print axioms one_cycle_row_count
#print axioms one_cycle_literal_count
#print axioms one_generated_cycle_row_count
#print axioms actual_generated_cycle_counts
#print axioms exact_f1_emitted_list_volume
#print axioms exact_f1_emitted_list_at_printed_sizes
end F5R62.PhysicalEmit
