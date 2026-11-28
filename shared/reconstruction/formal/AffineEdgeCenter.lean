import AffineEdgeModel
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Pi

open scoped BigOperators Polynomial

namespace AffineEdge

abbrev Kind (q : ℕ) := Option (Fin q)
abbrev Slot (q : ℕ) := (Kind q × Bool) ⊕ (Fin q × Kind q)

def complement {q : ℕ} (a : Bits q) : Bits q := fun i => !(a i)

def step {q : ℕ} (a : Bits q) : Kind q → Bits q
  | none => a
  | some t => flip t a

private theorem bit_ne_neg (b : Bool) : b ≠ !b := by cases b <;> decide

theorem step_injective {q : ℕ} (a : Bits q) : Function.Injective (step a) := by
  intro s t h
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some t =>
      exact (bit_ne_neg (a t) (by simpa [step] using congrFun h t)).elim
  | some s =>
    cases t with
    | none =>
      exact (bit_ne_neg (a s) (by simpa [step] using (congrFun h s).symm)).elim
    | some t =>
      by_contra hst
      have hn : s ≠ t := fun e => hst (congrArg some e)
      exact bit_ne_neg (a s) (by simpa [step, hn] using (congrFun h s).symm)

@[simp] theorem flip_complement {q : ℕ} (t : Fin q) (a : Bits q) :
    flip t (complement a) = complement (flip t a) := by
  funext j
  by_cases h : j = t
  · subst j
    simp [complement]
  · simp [complement, h]

/-- Hard physical columns have no matching slot (`none`) or the indicated
single matching slot (`some t`). -/
def hardWord {q : ℕ} (a : Bits q) (k : Kind q) : Word q :=
  (a, step (complement a) k)

def targetSlot {q : ℕ} : Kind q → Slot q
  | none => .inl (none, false)
  | some t => .inr (t, some t)

def placement {q : ℕ} : Slot q → Kind q × Kind q
  | .inl (k, _) => (none, k)
  | .inr (t, k) => (some t, k)

def wordAt {q : ℕ} (a : Bits q) (p : Kind q × Kind q) : Word q :=
  hardWord (step a p.1) p.2

theorem wordAt_injective {q : ℕ} (a : Bits q) : Function.Injective (wordAt a) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  have hij : i = j := step_injective a (congrArg Prod.fst h)
  subst j
  exact congrArg (fun s => (i, s)) (step_injective _ (congrArg Prod.snd h))

@[simp] private theorem target_second {q : ℕ} (a : Bits q) (k : Kind q) :
    (wordAt a (placement (targetSlot k))).2 = complement a := by
  cases k <;> simp [wordAt, placement, targetSlot, hardWord, step]

def intercept {q : ℕ} {F : Type*} [Zero F] [One F] : Slot q → F
  | .inl (_, false) => 1
  | .inl (_, true) => 0
  | .inr _ => 1

def gradient {q : ℕ} {F : Type*} [Zero F] [One F]
    (slope : Fin q → F) : Slot q → F
  | .inl (_, false) => 0
  | .inl (_, true) => 1
  | .inr (t, _) => slope t

def slotColumn {q : ℕ} {F H : Type*} [Field F] [AddCommGroup H] [Module F H]
    (slope : Fin q → F) (col : Bits q → Kind q → H) (a : Bits q) (i : Slot q) :
    H × H :=
  let z := col (step a (placement i).1) (placement i).2
  (intercept (F := F) i • z, gradient slope i • z)

/-- In any affine column relation at a center, all designated target
coefficients are zero. The index type retains even coincident column values. -/
def CenterCondition {q : ℕ} {F H : Type*} [Field F] [AddCommGroup H] [Module F H]
    (slope : Fin q → F) (col : Bits q → Kind q → H) : Prop :=
  ∀ a (x : Slot q → F), (∑ i, x i • slotColumn slope col a i) = 0 →
    ∀ k, x (targetSlot k) = 0

def collect {q : ℕ} {F : Type*} [Field F] (a : Bits q)
    (x : Slot q → F) (v : Word q) : F :=
  ∑ i, if wordAt a (placement i) = v then x i else 0

theorem sum_collect {q : ℕ} {F : Type*} [Field F] (a : Bits q)
    (x : Slot q → F) (u : Word q → F) :
    (∑ v, u v * collect a x v) = ∑ i, u (wordAt a (placement i)) * x i := by
  classical
  simp only [collect, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_ite]

private theorem intercept_target {q : ℕ} {F : Type*} [Field F] (k : Kind q) :
    intercept (F := F) (targetSlot k) = 1 := by
  cases k <;> rfl

private theorem slot_eq_of_placement {q : ℕ} {F : Type*} [Field F]
    (k : Kind q) (i : Slot q) (hp : placement i = placement (targetSlot k))
    (hi : intercept (F := F) i ≠ 0) : i = targetSlot k := by
  cases k <;> rcases i with ⟨j, b⟩ | ⟨s, j⟩
  · cases b <;> simp_all [placement, intercept, targetSlot]
  · simp [placement, targetSlot] at hp
  · simp [placement, targetSlot] at hp
  · simpa [placement, targetSlot] using hp

theorem collect_target {q : ℕ} {F : Type*} [Field F] (a : Bits q)
    (x : Slot q → F) (k : Kind q) :
    collect a (fun i => x i * intercept i) (wordAt a (placement (targetSlot k))) =
      x (targetSlot k) := by
  classical
  unfold collect
  rw [Finset.sum_eq_single (targetSlot k)]
  · simp [intercept_target]
  · intro i _ hi
    split
    next h =>
      have hn : intercept (F := F) i = 0 := by
        by_contra hn
        exact hi (slot_eq_of_placement k i (wordAt_injective a h) hn)
      simp [hn]
    next => rfl
  · simp

private theorem collect_known {q : ℕ} {F : Type*} [Field F]
    (sites : Fin q → F) (hn : ∀ t, sites t ≠ 0) (a : Bits q) (x : Slot q → F)
    (v : Word q) (t : Fin q) (hv : v.1 t = complement a t) :
    collect a (fun i => x i * intercept i) v +
      sites t * collect a (fun i => x i * gradient (fun s => -(sites s)⁻¹) i) v = 0 := by
  classical
  simp only [collect, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : wordAt a (placement i) = v
  · subst v
    rcases i with ⟨j, b⟩ | ⟨s, j⟩
    · exact (bit_ne_neg (a t) hv).elim
    · by_cases hs : t = s
      · subst s
        simp only [intercept, gradient, if_true, mul_one]
        rw [mul_left_comm (sites t), mul_neg, mul_inv_cancel₀ (hn t)]
        simp
      · simp [wordAt, placement, hardWord, step, complement, hs] at hv
  · simp [hi]

theorem centerCondition_of_paired {q : ℕ} {ι F : Type*} [Field F]
    {sites : Fin q → F} {C : ι → Word q → F} {P : Word q → Word q → F[X]}
    (hq : 2 ≤ q) (hinj : Function.Injective sites) (hn : ∀ t, sites t ≠ 0)
    (hp : PairedCondition sites C (q-2) P) :
    CenterCondition (fun t => -(sites t)⁻¹) (fun a k j => C j (hardWord a k)) := by
  intro a x hx k
  let f := collect a (fun i => x i * intercept i)
  let g := collect a (fun i => x i * gradient (fun t => -(sites t)⁻¹) i)
  let u := wordAt a (placement (targetSlot k))
  have hf (j : ι) : (∑ v, C j v * f v) = 0 := by
    rw [sum_collect]
    have h := congrArg (fun (p : (ι → F) × (ι → F)) => p.1 j) hx
    simpa only [slotColumn, Prod.fst_sum, Prod.smul_fst, Prod.fst_zero, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, wordAt, mul_comm, mul_left_comm] using h
  have hg (j : ι) : (∑ v, C j v * g v) = 0 := by
    rw [sum_collect]
    have h := congrArg (fun (p : (ι → F) × (ι → F)) => p.2 j) hx
    simpa only [slotColumn, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, wordAt, mul_comm, mul_left_comm] using h
  have hs (t : Fin q) (v : Word q) (h : v.1 t = u.2 t) : f v + sites t * g v = 0 :=
    collect_known sites hn a x v t (by simpa [u] using h)
  simpa only [f, u, collect_target] using affine_test_of_paired hq hinj hp u f g hf hg hs

end AffineEdge
