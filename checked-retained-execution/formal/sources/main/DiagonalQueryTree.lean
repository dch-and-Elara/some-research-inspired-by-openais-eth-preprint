import Std
import Lean.Elab.Tactic.Omega

/-!
An adaptive decoder chooses its next address from previous replies. A pattern
has two witness inputs with opposite required outputs. Off the supplied support
both return the public zero. The weighted lower bound is attained on an
actual run. The theorem for partial Boolean words proves the size of each
support cylinder directly from its fixed and free coordinates.
-/

namespace DiagonalQueryTree

inductive DecisionTree (Q : Type u) (R : Type v) : Type (max u v) where
  | leaf (output : Bool)
  | ask (query : Q) (next : R → DecisionTree Q R)

variable {Q : Type u} {R : Type v} {W : Type w}

def evaluate (oracle : Q → R) : DecisionTree Q R → Bool
  | .leaf output => output
  | .ask query next => evaluate oracle (next (oracle query))

def paid (cost : Q → Nat) (oracle : Q → R) : DecisionTree Q R → Nat
  | .leaf _ => 0
  | .ask query next => cost query + paid cost oracle (next (oracle query))

theorem complementary_filters (test : W → Bool) (xs : List W) :
    (xs.filter test).length + (xs.filter (fun x => !(test x))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : test x <;> simp only [List.filter_cons, h, Bool.not_false, Bool.not_true,
      if_true, if_false, List.length_cons, Bool.false_eq_true] <;> omega

/-- The per-query allowance is bounded on the original pool. Remaining
pools during an adaptive run are sublists, so their supports cannot grow. -/
theorem actual_path_capacity (zero : R) (oracle : W → Bool → Q → R)
    (test : Q → W → Bool) (cost : Q → Nat) (domain : List W)
    (off : ∀ w b q, test q w = false → oracle w b q = zero)
    (cap : ∀ q, (domain.filter (test q)).length ≤ cost q) (tree : DecisionTree Q R) :
    ∀ pool : List W, pool.Sublist domain → 0 < pool.length →
      (∀ w ∈ pool, ∀ b, evaluate (oracle w b) tree = b) →
      ∃ w ∈ pool, ∃ b, pool.length ≤ paid cost (oracle w b) tree := by
  induction tree with
  | leaf value =>
    intro pool _ hn correct
    obtain ⟨w, hw⟩ := List.length_pos_iff_exists_mem.mp hn
    have h0 : value = false := correct w hw false
    have h1 : value = true := correct w hw true
    cases h0.symm.trans h1
  | ask q next ih =>
    intro pool hsub hn correct
    let remaining := pool.filter (fun w => !(test q w))
    have hrsub : remaining.Sublist pool := List.filter_sublist
    have hs := complementary_filters (test q) pool
    have hit : (pool.filter (test q)).length ≤ cost q :=
      Nat.le_trans (hsub.filter (test q)).length_le (cap q)
    have split : pool.length ≤ cost q + remaining.length := by
      dsimp [remaining]
      omega
    have agree (w : W) (h : w ∈ remaining) : w ∈ pool ∧ test q w = false := by
      simpa [remaining] using h
    by_cases hr : 0 < remaining.length
    · have hc : ∀ w ∈ remaining, ∀ b, evaluate (oracle w b) (next zero) = b := by
        intro w hw b
        obtain ⟨hw', hzero⟩ := agree w hw
        simpa only [evaluate, off w b q hzero] using correct w hw' b
      obtain ⟨w, hw, b, htail⟩ := ih zero remaining (hrsub.trans hsub) hr hc
      obtain ⟨hw', hzero⟩ := agree w hw
      refine ⟨w, hw', b, ?_⟩
      simp only [paid, off w b q hzero]
      omega
    · obtain ⟨w, hw⟩ := List.length_pos_iff_exists_mem.mp hn
      refine ⟨w, hw, false, ?_⟩
      simp only [paid]
      omega

theorem paid_constant (c : Nat) (oracle : Q → R) (tree : DecisionTree Q R) :
    paid (fun _ => c) oracle tree = c * paid (fun _ => 1) oracle tree := by
  induction tree with
  | leaf value => simp [paid]
  | ask q next ih => simp [paid, ih, Nat.mul_add]

def allWords : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (allWords n).map (true :: ·) ++ (allWords n).map (false :: ·)

def cylinder : List (Option Bool) → List Bool → Bool
  | [], [] => true
  | none :: p, _ :: w => cylinder p w
  | some v :: p, h :: w => (v == h) && cylinder p w
  | _, _ => false

def freeBits : List (Option Bool) → Nat
  | [] => 0
  | none :: p => freeBits p + 1
  | some _ :: p => freeBits p

theorem allWords_length (n : Nat) : (allWords n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [allWords, List.length_append, List.length_map, ih, Nat.pow_succ]
                 omega

theorem cylinder_capacity (p : List (Option Bool)) :
    ((allWords p.length).filter (cylinder p)).length = 2 ^ freeBits p := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    cases x with
    | none =>
      simp [allWords, List.filter_map, Function.comp_def, cylinder, freeBits, ih, Nat.pow_succ]
      omega
    | some b =>
      cases b <;> simp [allWords, List.filter_map, Function.comp_def, cylinder, freeBits, ih]

theorem binary_cylinder_run {k : Nat} (zero : R)
    (oracle : List Bool → Bool → Q → R) (pattern : Q → List (Option Bool))
    (hlen : ∀ q, (pattern q).length = k)
    (off : ∀ w b q, cylinder (pattern q) w = false → oracle w b q = zero)
    (tree : DecisionTree Q R)
    (correct : ∀ w ∈ allWords k, ∀ b, evaluate (oracle w b) tree = b) :
    ∃ w ∈ allWords k, ∃ b,
       2 ^ k ≤ paid (fun q => 2 ^ freeBits (pattern q)) (oracle w b) tree := by
  have cap (q : Q) :
      ((allWords k).filter (cylinder (pattern q))).length ≤ 2 ^ freeBits (pattern q) := by
    have eqv := cylinder_capacity (pattern q)
    rw [hlen q] at eqv
    omega
  have hn : 0 < (allWords k).length := by rw [allWords_length]; exact Nat.two_pow_pos _
  obtain ⟨w, hw, b, h⟩ := actual_path_capacity zero oracle (fun q => cylinder (pattern q))
    (fun q => 2 ^ freeBits (pattern q)) (allWords k) off cap tree
    (allWords k) (List.Sublist.refl _) hn correct
  exact ⟨w, hw, b, by simpa only [allWords_length] using h⟩

/-- A real query budget can be imposed on every formal branch without
changing an evaluation on any input already obeying it. -/
def truncate : Nat → DecisionTree Q R → DecisionTree Q R
  | _, .leaf b => .leaf b
  | 0, .ask _ _ => .leaf false
  | n+1, .ask q next => .ask q (fun a => truncate n (next a))

theorem truncate_preserves (oracle : Q → R) :
    ∀ n (tree : DecisionTree Q R), paid (fun _ => 1) oracle tree ≤ n →
      evaluate oracle (truncate n tree) = evaluate oracle tree := by
  intro n
  induction n with
  | zero =>
    intro tree h
    cases tree with
    | leaf v => rfl
    | ask q next => simp [paid] at h
  | succ n ih =>
    intro tree h
    cases tree with
    | leaf v => rfl
    | ask q next =>
      simp only [paid] at h
      exact ih (next (oracle q)) (by omega)

def zeroTrace (zero : R) : DecisionTree Q R → List Q
  | .leaf _ => []
  | .ask q next => q :: zeroTrace zero (next zero)

theorem truncate_zero_length (zero : R) :
    ∀ n (tree : DecisionTree Q R), (zeroTrace zero (truncate n tree)).length ≤ n := by
  intro n
  induction n with
  | zero => intro tree; cases tree <;> simp [truncate, zeroTrace]
  | succ n ih =>
    intro tree
    cases tree with
    | leaf v => simp [truncate, zeroTrace]
    | ask q next =>
      simpa [truncate, zeroTrace] using ih (next zero)

def seen (test : Q → W → Bool) (trace : List Q) (w : W) : Bool :=
  trace.any (fun q => test q w)

theorem off_trace (zero : R) (oracle : W → Bool → Q → R)
    (test : Q → W → Bool) (off : ∀ w b q, test q w = false → oracle w b q = zero)
    (tree : DecisionTree Q R) (w : W) (b : Bool)
    (missing : seen test (zeroTrace zero tree) w = false) :
    evaluate (oracle w b) tree = evaluate (fun _ => zero) tree := by
  induction tree with
  | leaf _ => rfl
  | ask q next ih =>
    have hq : test q w = false ∧ seen test (zeroTrace zero (next zero)) w = false := by
      simpa [seen, zeroTrace] using missing
    simpa only [evaluate, off w b q hq.1] using ih zero hq.2

theorem filter_union_count (p q : W → Bool) (xs : List W) :
    (xs.filter (fun x => p x || q x)).length ≤
      (xs.filter p).length + (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;>
      simp [hp, hq] <;> omega

theorem filter_inter_count (p q : W → Bool) (xs : List W) :
    (xs.filter p).length + (xs.filter q).length ≤
      xs.length + (xs.filter (fun x => p x && q x)).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;>
      simp [hp, hq] <;> omega

theorem filter_mono_count (p q : W → Bool) (xs : List W)
    (hle : ∀ w ∈ xs, p w = true → q w = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have htail := ih (fun w hw => hle w (List.mem_cons_of_mem _ hw))
    have hx := hle x (List.mem_cons_self)
    cases hp : p x <;> cases hq : q x <;>
      simp [hp, hq] at * <;> omega

theorem seen_count (test : Q → W → Bool) (domain : List W) (cap : Nat)
    (hcap : ∀ q, (domain.filter (test q)).length ≤ cap) (qs : List Q) :
    (domain.filter (seen test qs)).length ≤ cap * qs.length := by
  induction qs with
  | nil => simp [seen]
  | cons q qs ih =>
    have h := filter_union_count (test q) (seen test qs) domain
    have hc := hcap q
    simp only [List.length_cons, Nat.mul_succ]
    change (domain.filter (fun w => test q w || seen test qs w)).length ≤ _
    omega

/-- Number of correctly answered input pairs in the uniform two-witness
experiment. The tree may return either answer on every unvisited pattern. -/
def successes (oracle : W → Bool → Q → R) (tree : DecisionTree Q R) (domain : List W) : Nat :=
  (domain.filter (fun w => !(evaluate (oracle w false) tree))).length +
  (domain.filter (fun w => evaluate (oracle w true) tree)).length

theorem one_seed_bound (zero : R) (oracle : W → Bool → Q → R) (test : Q → W → Bool)
    (domain : List W) (cap n : Nat) (tree : DecisionTree Q R)
    (off : ∀ w b q, test q w = false → oracle w b q = zero)
    (hcap : ∀ q, (domain.filter (test q)).length ≤ cap)
    (budget : ∀ w ∈ domain, ∀ b, paid (fun _ => 1) (oracle w b) tree ≤ n) :
    successes oracle tree domain ≤ domain.length + cap * n := by
  let cut := truncate n tree
  let tr := zeroTrace zero cut
  let p := fun w => !(evaluate (oracle w false) tree)
  let q := fun w => evaluate (oracle w true) tree
  have keep (w) (hw : w ∈ domain) (b) :
      evaluate (oracle w b) cut = evaluate (oracle w b) tree :=
    truncate_preserves _ n tree (budget w hw b)
  have both : ∀ w ∈ domain, (p w && q w) = true → seen test tr w = true := by
    intro w hw good
    cases h : seen test tr w with
    | true => rfl
    | false =>
      have e0 := off_trace zero oracle test off cut w false h
      have e1 := off_trace zero oracle test off cut w true h
      rw [keep w hw false] at e0
      rw [keep w hw true] at e1
      have eqv := e0.trans e1.symm
      simp [p, q, eqv] at good
  have h1 := filter_inter_count p q domain
  have h2 := filter_mono_count (fun w => p w && q w) (seen test tr) domain both
  have h3 := seen_count test domain cap hcap tr
  have ht : tr.length ≤ n := truncate_zero_length zero n tree
  have h4 : cap * tr.length ≤ cap * n := Nat.mul_le_mul_left cap ht
  change (domain.filter p).length + (domain.filter q).length ≤ _
  omega

/-- Summation over a finite list of random seeds, allowing repetitions. -/
theorem finite_seed_bound {S : Type z} (zero : R) (oracle : W → Bool → Q → R)
    (test : Q → W → Bool) (domain : List W) (cap n : Nat)
    (tree : S → DecisionTree Q R) (seeds : List S)
    (off : ∀ w b q, test q w = false → oracle w b q = zero)
    (hcap : ∀ q, (domain.filter (test q)).length ≤ cap)
    (budget : ∀ s w, w ∈ domain → ∀ b, paid (fun _ => 1) (oracle w b) (tree s) ≤ n) :
    (seeds.map (fun s => successes oracle (tree s) domain)).sum ≤
      seeds.length * (domain.length + cap*n) := by
  induction seeds with
  | nil => simp
  | cons s ss ih =>
    have h := one_seed_bound zero oracle test domain cap n (tree s) off hcap (budget s)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

#print axioms actual_path_capacity
#print axioms paid_constant
#print axioms cylinder_capacity
#print axioms binary_cylinder_run
#print axioms truncate_preserves
#print axioms one_seed_bound
#print axioms finite_seed_bound

end DiagonalQueryTree
