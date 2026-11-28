import J1R15Token

/-! Executable typed-alphabet composition: prepare the candidate's
indexed tape once, produce each copied-slot token by source bit lookups,
then run the already verified scalar register accumulation. -/
namespace J1R15
open AOracleMachineTime A1R10 J1R14Query J1MainSourcePlacement MainProbe

abbrev SlotInput := List Bool × BasisRows

def produceTokens (P G A : File) (t g : List Bool) : List SlotInput → Meter (List SignedUnit)
  | [] => ⟨[],1⟩
  | a::as =>
    let first := rawProduce P G A a.1 t g a.2
    let rest := produceTokens P G A t g as
    ⟨first.result :: rest.result, first.steps+rest.steps+1⟩

theorem produceTokens_result (P G A : File) (t g : List Bool) (xs : List SlotInput) :
    (produceTokens P G A t g xs).result =
    xs.map (fun a => (rawProduce P G A a.1 t g a.2).result) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [produceTokens,ih]

theorem produceTokens_cost (P G A : File) (t g : List Bool) (xs : List SlotInput) (K : ℕ)
    (h : ∀ a ∈ xs, (rawProduce P G A a.1 t g a.2).steps ≤ K) :
    (produceTokens P G A t g xs).steps ≤ xs.length*(K+1)+1 := by
  induction xs with
  | nil => simp [produceTokens]
  | cons a as ih =>
    have hf := h a List.mem_cons_self
    have hr := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    change (rawProduce P G A a.1 t g a.2).steps + (produceTokens P G A t g as).steps+1 ≤ _
    calc
      _ ≤ K+(as.length*(K+1)+1)+1 := Nat.add_le_add_right (Nat.add_le_add hf hr) 1
      _ = _ := by simp only [List.length_cons,Nat.succ_mul]; ac_rfl

theorem amount_injective : Function.Injective SignedUnit.amount := by
  intro x y h
  cases x <;> cases y <;> simp_all [SignedUnit.amount]

def executeRow {p : ℕ} (hp : 0<p) (a : Word p) (P G : File) (t g : List Bool)
    (keys : List (List Bool)) (raw : List Bool) (slots : List SlotInput) : Meter (Word p) :=
  let cand := attachCandidates keys raw
  let produced := produceTokens P G cand.result t g slots
  let checked := measureTape hp a produced.result
  ⟨checked.result,cand.steps+produced.steps+checked.steps⟩

section Source
variable {q r n M h d p : ℕ} {E F A : Type*} [Fintype E]
variable (data : IncidenceData (Fin q) (Fin r) E (Fin n) F)
variable (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h)
variable (order : Fin M ≃ E)
variable (pin : A → E) (diag : ∀ a, (data.cell (pin a)).1 = (data.cell (pin a)).2)
variable (interval : Finset ℕ) (hz : 0 ∉ interval)

def sourceSlots (c : Fin h) (b : Fin q → LocalBasis (Fin r))
    (e : Fin d ≃ Cell (Fin q) (Fin r)) : List SlotInput :=
  List.ofFn fun j => (positionCode (c,e j),fullBasisBits b (e j))

theorem sourceTokens_exact (x : Fin n → Bool) (t : Fin q) (g : Fin r) (c : Fin h)
    (b : Exceptional (Fin q) (Fin r) interval) (e : Fin d ≃ Cell (Fin q) (Fin r)) :
    (produceTokens (placedFile data cap order) (groupFile data.wordVar)
      (indexedCandidate (n:=n) (List.ofFn x)).result (finWord t) (finWord g)
      (sourceSlots c b.val e)).result =
      actualTokens (sourceLayout data h cap pin diag) interval hz e t g (c,b) x := by
  rw [produceTokens_result,sourceSlots,List.map_ofFn]
  unfold actualTokens
  congr 1
  funext j
  apply amount_injective
  change (rawProduce _ _ _ (positionCode (c,e j)) _ _ (fullBasisBits b.val (e j))).result.amount = _
  rw [← produceSlot_raw data cap order x t g c b.val (e j)]
  rw [produceSlot_amount data cap order pin diag interval hz]
  exact (signedUnit_exact _
    (slotAmount_signed (sourceLayout data h cap pin diag) interval hz t g (c,b) x (e j))).symm

def slotBudget (q r n M h : ℕ) : ℕ :=
  maskBudget q r n M h + (q*(16*Nat.clog 2 r+12+3)+1) + 3

theorem sourceTokens_cost (x : Fin n → Bool) (t : Fin q) (g : Fin r) (c : Fin h)
    (b : Fin q → LocalBasis (Fin r)) (e : Fin d ≃ Cell (Fin q) (Fin r)) :
    (produceTokens (placedFile data cap order) (groupFile data.wordVar)
      (indexedCandidate (n:=n) (List.ofFn x)).result (finWord t) (finWord g)
      (sourceSlots c b e)).steps ≤ d*(slotBudget q r n M h+1)+1 := by
  have hb := produceTokens_cost (placedFile data cap order) (groupFile data.wordVar)
    (indexedCandidate (n:=n) (List.ofFn x)).result (finWord t) (finWord g) (sourceSlots c b e)
    (slotBudget q r n M h) (by
      intro j hj
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
      change (rawProduce _ _ _ (positionCode (c,e i)) _ _ (fullBasisBits b (e i))).steps ≤ _
      rw [← produceSlot_raw data cap order x t g c b (e i)]
      exact produceSlot_cost data cap order x t g c b (e i))
  simpa only [sourceSlots,List.length_ofFn] using hb

/-- This is the full measurement of one row at one candidate x. Public
register files and the current row's input addresses are serialized first;
they are not counter answers, precomputed row contributions or hidden
candidate-dependent masks. -/
noncomputable def sourceExecution (hp : 0<p) (a : Word p) (x : Fin n → Bool)
    (t : Fin q) (g : Fin r) (c : Fin h) (b : Fin q → LocalBasis (Fin r))
    (e : Fin d ≃ Cell (Fin q) (Fin r)) : Meter (Word p) :=
  executeRow hp a (placedFile data cap order) (groupFile data.wordVar) (finWord t) (finWord g)
    (List.ofFn (@finWord n)) (List.ofFn x) (sourceSlots c b e)

theorem sourceExecution_exact (hp : 0<p) (a : Word p) (x : Fin n → Bool) (t : Fin q)
    (g : Fin r) (c : Fin h) (b : Exceptional (Fin q) (Fin r) interval)
    (e : Fin d ≃ Cell (Fin q) (Fin r)) :
    wordRead (sourceExecution data cap order hp a x t g c b.val e).result =
      wordRead a + (rowRead (sourceLayout data h cap pin diag)
        (printedBasis (sourceLayout data h cap pin diag) interval hz) t g (c,b) x : ZMod (2^p)) := by
  dsimp only [sourceExecution,executeRow]
  change wordRead (measureTape hp a (produceTokens (placedFile data cap order)
    (groupFile data.wordVar) (indexedCandidate (n:=n) (List.ofFn x)).result (finWord t) (finWord g)
    (sourceSlots c b.val e)).result).result = _
  rw [sourceTokens_exact data cap order pin diag interval hz]
  exact (actual_measure_tape (sourceLayout data h cap pin diag) interval hz hp a e t g (c,b) x).1

theorem sourceExecution_cost (hp : 0<p) (a : Word p) (x : Fin n → Bool) (t : Fin q)
    (g : Fin r) (c : Fin h) (b : Exceptional (Fin q) (Fin r) interval)
    (e : Fin d ≃ Cell (Fin q) (Fin r)) :
    (sourceExecution data cap order hp a x t g c b.val e).steps ≤
      (n*(2*Nat.clog 2 n+3)+1) + (d*(slotBudget q r n M h+1)+1) + d*(2+32*(p+1)^2) := by
  let T := (produceTokens (placedFile data cap order) (groupFile data.wordVar)
    (indexedCandidate (n:=n) (List.ofFn x)).result (finWord t) (finWord g)
    (sourceSlots c b.val e))
  have hC := indexedCandidate_setup_cost n (List.ofFn x)
  have hT : T.steps ≤ d*(slotBudget q r n M h+1)+1 :=
    sourceTokens_cost data cap order x t g c b.val e
  have hlen : T.result.length = d := by
    dsimp only [T]
    rw [produceTokens_result,List.length_map]
    simp [sourceSlots]
  have hreg : (measureTape hp a T.result).steps ≤ d*(2+32*(p+1)^2) := by
    simpa only [hlen] using measureTape_cost hp a T.result
  change (indexedCandidate (n:=n) (List.ofFn x)).steps + T.steps + (measureTape hp a T.result).steps ≤ _
  exact Nat.add_le_add (Nat.add_le_add hC hT) hreg
end Source

#print axioms produceTokens_result
#print axioms produceTokens_cost
#print axioms amount_injective
#print axioms sourceTokens_exact
#print axioms sourceTokens_cost
#print axioms sourceExecution_exact
#print axioms sourceExecution_cost
end J1R15
