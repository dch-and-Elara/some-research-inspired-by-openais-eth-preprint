import J1R15Compare

/-! The printed first-sweep predicate on one candidate: run every
copied exceptional measurement row and require exact agreement with its
address register. A raw executable entry point is given before the source
interpretation. Producing the supplied ordered row/target tapes and
enumerating successive private vectors remain separate work. -/
namespace J1R15
open AOracleMachineTime A1R10 J1R14Query J1MainSourcePlacement MainProbe

def meterAll {T : Type*} (f : T → Meter Bool) : List T → Meter Bool
  | [] => ⟨true,1⟩
  | t::ts =>
    let a := f t
    let b := meterAll f ts
    ⟨a.result && b.result,a.steps+b.steps+1⟩

theorem meterAll_true {T : Type*} (f : T → Meter Bool) (xs : List T) :
    (meterAll f xs).result = true ↔ ∀ t ∈ xs, (f t).result = true := by
  induction xs with
  | nil => simp [meterAll]
  | cons a xs ih => simp [meterAll,ih]

theorem meterAll_cost {T : Type*} (f : T → Meter Bool) (xs : List T) (K : ℕ)
    (h : ∀ t ∈ xs, (f t).steps ≤ K) :
    (meterAll f xs).steps ≤ xs.length*(K+1)+1 := by
  induction xs with
  | nil => simp [meterAll]
  | cons a as ih =>
    have hf := h a List.mem_cons_self
    have hr := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    change (f a).steps+(meterAll f as).steps+1 ≤ _
    calc
      _ ≤ K+(as.length*(K+1)+1)+1 := Nat.add_le_add_right (Nat.add_le_add hf hr) _
      _ = _ := by simp only [List.length_cons,Nat.succ_mul]; ac_rfl

abbrev RawTarget (p : ℕ) := List SlotInput × Word p

def rawFibreTest {p : ℕ} (hp : 0<p) (a : Word p) (P G : File) (t g : List Bool)
    (keys : List (List Bool)) (raw : List Bool) (rows : List (RawTarget p)) : Meter Bool :=
  meterAll (fun row => compareWord (executeRow hp a P G t g keys raw row.1) row.2) rows

section Source
variable {q r n M h d p c₀ : ℕ} {E F A : Type*} [Fintype E]
variable (data : IncidenceData (Fin q) (Fin r) E (Fin n) F)
variable (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h)
variable (order : Fin M ≃ E)
variable (pin : A → E) (diag : ∀ a, (data.cell (pin a)).1 = (data.cell (pin a)).2)
variable (interval : Finset ℕ) (hz : 0 ∉ interval)

local notation "D₀" => Fintype.card (Cell (Fin q) (Fin r))
local notation "L₀" => sourceLayout data h cap pin diag
abbrev GroupRow (q r h : ℕ) (interval : Finset ℕ) :=
  Fin h × Exceptional (Fin q) (Fin r) interval

def queryTargets (e : Fin d ≃ Cell (Fin q) (Fin r))
    (ords : Fin c₀ ≃ GroupRow q r h interval)
    (y : GroupRow q r h interval → Box D₀) : List (RawTarget p) :=
  List.ofFn fun i => (sourceSlots (ords i).1 (ords i).2.val e,natWord p (y (ords i)).val)

noncomputable def sourceFibreTest (hp : 0<p) (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (e : Fin d ≃ Cell (Fin q) (Fin r)) (ords : Fin c₀ ≃ GroupRow q r h interval)
    (y : GroupRow q r h interval → Box D₀) : Meter Bool :=
  rawFibreTest hp (natWord p D₀) (placedFile data cap order) (groupFile data.wordVar)
    (finWord t) (finWord g) (List.ofFn (@finWord n)) (List.ofFn x) (queryTargets interval e ords y)

theorem sourceFibreTest_exact (hp : 0<p) (hwide : 2*D₀ < 2^p)
    (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (e : Fin d ≃ Cell (Fin q) (Fin r)) (ords : Fin c₀ ≃ GroupRow q r h interval)
    (y : GroupRow q r h interval → Box D₀) :
    (sourceFibreTest data cap order interval hp x t g e ords y).result = true ↔
      ∀ z, rowRead L₀ (printedBasis L₀ interval hz) t g z x = boxValue (y z) := by
  rw [sourceFibreTest,rawFibreTest,meterAll_true]
  constructor
  · intro h z
    let j := ords.symm z
    have hz' : ords j = z := ords.apply_symm_apply z
    have hj := h _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    change (sourceRowTest data cap order interval hp x t g (ords j).1 (ords j).2 e
      (y (ords j))).result = true at hj
    rw [sourceRowTest_exact data cap order pin diag interval hz hp hwide,
      decide_eq_true_eq,hz'] at hj
    exact hj
  · intro h tgt htgt
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp htgt
    change (sourceRowTest data cap order interval hp x t g (ords j).1 (ords j).2 e
      (y (ords j))).result = true
    rw [sourceRowTest_exact data cap order pin diag interval hz hp hwide,decide_eq_true_eq]
    exact h (ords j)


theorem sourceFibreTest_firstScan (hp : 0<p) (hwide : 2*D₀ < 2^p)
    (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (hx : x ∈ privateCube L₀ t g)
    (e : Fin d ≃ Cell (Fin q) (Fin r)) (ords : Fin c₀ ≃ GroupRow q r h interval)
    (y : GroupRow q r h interval → Box D₀) :
    (sourceFibreTest data cap order interval hp x t g e ords y).result = true ↔
      x ∈ firstScan L₀ (printedBasis L₀ interval hz) t g (fun _ z => boxValue (y z)) := by
  classical
  rw [sourceFibreTest_exact data cap order pin diag interval hz hp hwide]
  simp only [firstScan,Finset.mem_filter,hx,true_and]

theorem sourceFibreTest_cost (hp : 0<p) (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (e : Fin d ≃ Cell (Fin q) (Fin r)) (ords : Fin c₀ ≃ GroupRow q r h interval)
    (y : GroupRow q r h interval → Box D₀) :
    (sourceFibreTest data cap order interval hp x t g e ords y).steps ≤
      c₀ * ((n*(2*Nat.clog 2 n+3)+1) + (d*(slotBudget q r n M h+1)+1) +
        d*(2+32*(p+1)^2) + 4*p + 1 + 1) + 1 := by
  let K := (n*(2*Nat.clog 2 n+3)+1) + (d*(slotBudget q r n M h+1)+1) +
    d*(2+32*(p+1)^2) + 4*p + 1
  have hb := meterAll_cost (fun row : RawTarget p => compareWord
    (executeRow hp (natWord p D₀) (placedFile data cap order) (groupFile data.wordVar)
      (finWord t) (finWord g) (List.ofFn (@finWord n)) (List.ofFn x) row.1) row.2)
    (queryTargets interval e ords y) K (by
      intro b hb
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      exact sourceRowTest_cost data cap order interval hp x t g (ords i).1 (ords i).2 e (y (ords i)))
  change _ ≤ c₀*(K+1)+1
  simpa only [queryTargets,List.length_ofFn] using hb
end Source

#print axioms meterAll_true
#print axioms meterAll_cost
#print axioms sourceFibreTest_exact
#print axioms sourceFibreTest_cost
#print axioms sourceFibreTest_firstScan
end J1R15
