import AffineCostCoefficients
import AffineCostExecute
import AffineCostOutput

open AffineEdge
open scoped Polynomial

namespace AffineCost

open Bit

def bitWords : (q : ℕ) → List (Bits q)
  | 0 => [fun i => Fin.elim0 i]
  | n+1 => (bitWords n).map (Fin.cons false) ++ (bitWords n).map (Fin.cons true)

theorem bitWords_length (q : ℕ) : (bitWords q).length = 2^q := by
  induction q with
  | zero => decide
  | succ q ih => simp [bitWords, ih, pow_succ, Nat.mul_two]

theorem mem_bitWords (q : ℕ) (a : Bits q) : a ∈ bitWords q := by
  induction q with
  | zero =>
    have h : a = fun i => Fin.elim0 i := funext fun i => Fin.elim0 i
    simp [bitWords, h]
  | succ q ih =>
    have ht := ih (Fin.tail a)
    have he : Fin.cons (a 0) (Fin.tail a) = a := Fin.cons_self_tail _
    cases h : a 0
    · simp [bitWords]
      exact Or.inl ⟨Fin.tail a, ht, by rwa [h] at he⟩
    · simp [bitWords]
      exact Or.inr ⟨Fin.tail a, ht, by rwa [h] at he⟩

def words (q : ℕ) : List (AffineEdge.Word q) := (bitWords q).product (bitWords q)

theorem words_length (q : ℕ) : (words q).length = 4^q := by
  change ((bitWords q) ×ˢ (bitWords q)).length = 4^q
  rw [List.length_product, bitWords_length, ← mul_pow]
  rfl

theorem mem_words (q : ℕ) (u : AffineEdge.Word q) : u ∈ words q := by
  rcases u with ⟨a,b⟩
  change (a,b) ∈ (bitWords q) ×ˢ (bitWords q)
  exact List.mem_product.mpr ⟨mem_bitWords q a,mem_bitWords q b⟩

abbrev Task (q : ℕ) := AffineEdge.Word q × AffineEdge.Word q × Fin q

def tasks (q : ℕ) : List (Task q) := (words q).product ((words q).product (List.finRange q))

theorem tasks_length (q : ℕ) : (tasks q).length = (4^q)*(4^q)*q := by
  change ((words q) ×ˢ ((words q) ×ˢ (List.finRange q))).length = _
  simp [List.length_product, words_length, Nat.mul_assoc]

theorem mem_tasks (q : ℕ) (t : Task q) : t ∈ tasks q := by
  rcases t with ⟨u,v,k⟩
  change (u,v,k) ∈ (words q) ×ˢ ((words q) ×ˢ List.finRange q)
  exact List.mem_product.mpr ⟨mem_words q u,
    List.mem_product.mpr ⟨mem_words q v,List.mem_finRange _⟩⟩

def taskExpr (t : Task q) : Expr q := coefficientExpr t.1 t.2.1 t.2.2

def coreSize (D q : ℕ) : ℕ := 1024*(q+1)*D

theorem taskExpr_size (t : Task q) : (taskExpr t).nodes ≤ coreSize (4^q) q := by
  apply (coefficientExpr_nodes _ _ _).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)

def mapRun {α β : Type} (f : α → Run β) : List α → Run (List β)
  | [] => ⟨[],8⟩
  | x :: xs =>
    let y := f x
    let ys := mapRun f xs
    ⟨y.value :: ys.value, 16+y.steps+ys.steps⟩

theorem mapRun_value {α β : Type} (f : α → Run β) (xs : List α) :
    (mapRun f xs).value = xs.map fun x => (f x).value := by
  induction xs <;> simp [mapRun, *]

theorem mapRun_steps {α β : Type} (f : α → Run β) (xs : List α) (N : ℕ)
    (h : ∀ x ∈ xs, (f x).steps ≤ N) :
    (mapRun f xs).steps ≤ 8+xs.length*(16+N) := by
  induction xs with
  | nil => simp [mapRun]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih fun y hy => h y (by simp [hy])
    simp only [mapRun,List.length_cons,Nat.add_mul,one_mul]
    omega

/-- The additional charge writes the four magnitude strings of the resulting
fraction, with separators. -/
def expressionRun (as : List Fraction) (e : Expr q) : Run Fraction :=
  let r := e.execute as
  ⟨r.value, r.steps+(emitFraction r.value).steps⟩

def coefficientRun (as : List Fraction) (t : Task q) : Run Fraction :=
  expressionRun as (taskExpr t)

def matrixRun (as : List Fraction) (q : ℕ) : Run (List Fraction) :=
  mapRun (coefficientRun as) (tasks q)

theorem matrixRun_value (as : List Fraction) (q : ℕ) :
    (matrixRun as q).value = (tasks q).map fun t => ((taskExpr t).execute as).value :=
  mapRun_value _ _

def coefficientBound (D q L : ℕ) : ℕ :=
  let N := coreSize D q
  let U := (L+3)*N
  N * Expr.budget q U + 32*(U+1)

/-- Polynomial bit-step budget for executing and writing a compiled schedule. -/
def executionBound (D q L : ℕ) : ℕ := 8+D*D*q*(16+coefficientBound D q L)

theorem coefficientRun_size (as : List Fraction) (L : ℕ)
    (h : ∀ a ∈ as, a.size ≤ L) (t : Task q) :
    (coefficientRun as t).value.size ≤ (L+3)*coreSize (4^q) q :=
  (Expr.execute_size as L h (taskExpr t)).trans (Nat.mul_le_mul_left _ (taskExpr_size t))

theorem matrixRun_step_bound (as : List Fraction) (q L : ℕ)
    (h : ∀ a ∈ as, a.size ≤ L) :
    (matrixRun as q).steps ≤ executionBound (4^q) q L := by
  unfold matrixRun executionBound
  rw [← tasks_length]
  apply mapRun_steps
  intro t _
  have h₁ := Expr.execute_steps as L h (taskExpr t) _ (taskExpr_size t)
  have h₂ := coefficientRun_size as L h t
  have he := emitFraction_steps (coefficientRun as t).value
  unfold coefficientRun expressionRun coefficientBound at *
  dsimp at *
  omega

theorem coefficientRun_correct (as : List Fraction) (hv : ∀ a ∈ as, a.valid)
    (t : Task q) :
    (coefficientRun as t).value.valid ∧
      (coefficientRun as t).value.rat =
        (rowPolynomial (bitSites as) t.1 t.2.1).coeff t.2.2.val := by
  refine ⟨Expr.execute_valid as hv (taskExpr t), ?_⟩
  change ((taskExpr t).execute as).value.rat = _
  exact (Expr.execute_rat as hv (taskExpr t)).trans
    (coefficientExpr_eval (bitSites as : Fin q → ℚ) t.1 t.2.1 t.2.2)

theorem matrixRun_correct (as : List Fraction) (hv : ∀ a ∈ as, a.valid)
    (hq : 2 ≤ q) (hi : Function.Injective (bitSites as : Fin q → ℚ))
    (hn : ∀ t : Fin q, bitSites as t ≠ 0) :
    ∃ P, PairedCondition (bitSites as) (binaryEncoder q) (q-2) P ∧
      (matrixRun as q).value.map Fraction.rat =
        (tasks q).map (fun t => (P t.1 t.2.1).coeff t.2.2.val) := by
  refine ⟨rowPolynomial (bitSites as), rowPolynomial_correct _ hq hi hn, ?_⟩
  rw [matrixRun_value, List.map_map]
  congr 1
  funext t
  exact (coefficientRun_correct as hv t).2

/-- Consume a computed schedule. No expression is reconstructed here. -/
def runCompiled (as : List Fraction) (c : Run (List (Task q × Expr q))) :
    Run (List Fraction) :=
  let r := mapRun (fun p : Task q × Expr q => expressionRun as p.2) c.value
  ⟨r.value, c.steps+r.steps⟩

private theorem mapRun_map {α β γ : Type} (f : β → Run γ) (g : α → β) (l : List α) :
    mapRun f (l.map g) = mapRun (fun x => f (g x)) l := by
  induction l <;> simp [mapRun, *]

theorem runCompiled_eq (as : List Fraction) (c : Run (List (Task q × Expr q)))
    (hc : c.value = (tasks q).map (fun t => (t,taskExpr t))) :
    runCompiled as c = ⟨(matrixRun as q).value, c.steps+(matrixRun as q).steps⟩ := by
  simp only [runCompiled, hc, mapRun_map, matrixRun]
  rfl

theorem runCompiled_bound (as : List Fraction) (c : Run (List (Task q × Expr q))) (L : ℕ)
    (h : ∀ a ∈ as, a.size ≤ L)
    (hc : c.value = (tasks q).map (fun t => (t,taskExpr t))) :
    (runCompiled as c).steps ≤ c.steps+executionBound (4^q) q L := by
  rw [runCompiled_eq as c hc]
  exact Nat.add_le_add_left (matrixRun_step_bound as q L h) _

theorem runCompiled_correct (as : List Fraction) (c : Run (List (Task q × Expr q)))
    (hc : c.value = (tasks q).map (fun t => (t,taskExpr t))) (hv : ∀ a ∈ as, a.valid)
    (hq : 2 ≤ q) (hi : Function.Injective (bitSites as : Fin q → ℚ))
    (hn : ∀ t : Fin q, bitSites as t ≠ 0) :
    ∃ P, PairedCondition (bitSites as) (binaryEncoder q) (q-2) P ∧
      (runCompiled as c).value.map Fraction.rat =
        (tasks q).map (fun t => (P t.1 t.2.1).coeff t.2.2.val) := by
  rw [runCompiled_eq as c hc]
  exact matrixRun_correct as hv hq hi hn

/-- Emit a list of self-delimiting bit chunks, in compiler schedule order.
Writing a chunk uses the bit operations of the encoder rather than a
unit-cost rational output operation. -/
def runCompiledOutput (as : List Fraction) (c : Run (List (Task q × Expr q))) :
    Run (List Bit.Word) :=
  let r := mapRun (fun p : Task q × Expr q =>
    let z := p.2.execute as
    let w := emitFraction z.value
    ⟨w.value,z.steps+w.steps⟩) c.value
  ⟨r.value,c.steps+r.steps⟩

private theorem mapRun_payload {α β γ : Type} (f : α → Run β) (g : β → γ) (l : List α) :
    mapRun (fun x => ⟨g (f x).value, (f x).steps⟩) l =
      ⟨(mapRun f l).value.map g, (mapRun f l).steps⟩ := by
  induction l <;> simp [mapRun, *]

theorem runCompiledOutput_eq (as : List Fraction) (c : Run (List (Task q × Expr q))) :
    runCompiledOutput as c =
      ⟨(runCompiled as c).value.map (fun a => (emitFraction a).value),
        (runCompiled as c).steps⟩ := by
  have he := mapRun_payload (fun p : Task q × Expr q => expressionRun as p.2)
    (fun a => (emitFraction a).value) c.value
  change mapRun (fun p : Task q × Expr q =>
    ⟨(emitFraction (p.2.execute as).value).value,
      (p.2.execute as).steps+(emitFraction (p.2.execute as).value).steps⟩) c.value = _ at he
  simp only [runCompiledOutput, runCompiled, he]

/-- Compose the exact output writer with any compiler of the uniform schedule.
The caller supplies that compiler's separately proved step count. -/
theorem runCompiledOutput_correct (as : List Fraction) (c : Run (List (Task q × Expr q)))
    (hc : c.value = (tasks q).map (fun t => (t,taskExpr t))) (hv : ∀ a ∈ as, a.valid)
    (hq : 2 ≤ q) (hi : Function.Injective (bitSites as : Fin q → ℚ))
    (hn : ∀ t : Fin q, bitSites as t ≠ 0) :
    ∃ P, PairedCondition (bitSites as) (binaryEncoder q) (q-2) P ∧
      (runCompiledOutput as c).value.map (fun s => (readFraction s).map fun p => p.1.rat) =
        (tasks q).map (fun t => some ((P t.1 t.2.1).coeff t.2.2.val)) := by
  obtain ⟨P,hP,he⟩ := runCompiled_correct as c hc hv hq hi hn
  refine ⟨P,hP,?_⟩
  rw [runCompiledOutput_eq]
  have e := congrArg (List.map some) he
  simpa [List.map_map, Function.comp_def] using e

theorem runCompiledOutput_bound (as : List Fraction) (c : Run (List (Task q × Expr q))) (L : ℕ)
    (h : ∀ a ∈ as, a.size ≤ L)
    (hc : c.value = (tasks q).map (fun t => (t,taskExpr t))) :
    (runCompiledOutput as c).steps ≤ c.steps+executionBound (4^q) q L := by
  rw [runCompiledOutput_eq]
  exact runCompiled_bound as c L h hc

theorem runCompiledOutput_valid (as : List Fraction) (c : Run (List (Task q × Expr q)))
    (hc : c.value = (tasks q).map (fun t => (t,taskExpr t))) (hv : ∀ a ∈ as, a.valid)
    (s : Bit.Word) (hs : s ∈ (runCompiledOutput as c).value) :
    ∃ a, readFraction s = some (a,[]) ∧ a.valid := by
  rw [runCompiledOutput_eq, runCompiled_eq as c hc, matrixRun_value] at hs
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
  exact ⟨_, readFraction_emitted _, Expr.execute_valid as hv (taskExpr t)⟩

end AffineCost
