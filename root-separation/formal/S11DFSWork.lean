
import S11Literal
import S11Partition

namespace S11

open scoped BigOperators

/-- The actual DFS choice counter. It is incremented on every visited
    prefix, including the root and a complete exponent vector. A call
    with zero remaining budget does not visit a prefix. -/
def prefixVisits : List ℕ → ℕ → ℕ
  | [], p => if p = 0 then 0 else 1
  | w :: ws, p =>
    if p = 0 then 0
    else 1 + ((List.range ((p-1)/w+1)).map fun b => prefixVisits ws (p-w*b)).sum

def countedFold {A : Type*} : List ℕ → ℕ → (A → List ℕ → A) → A × ℕ → A × ℕ
  | [], p, step, st => if p = 0 then st else (step st.1 [], st.2 + 1)
  | w :: ws, p, step, st =>
    if p = 0 then st else
      (List.range ((p-1)/w+1)).foldl
        (fun st b => countedFold ws (p-w*b) (fun a bs => step a (b :: bs)) st)
        (st.1, st.2+1)

private theorem foldl_pair_first {A B : Type*} (l : List B) (f : A × ℕ → B → A × ℕ)
    (g : A → B → A) (h : ∀ a b, (f a b).1 = g a.1 b) (x : A × ℕ) :
    (l.foldl f x).1 = l.foldl g x.1 := by
  induction l generalizing x with
  | nil => rfl
  | cons b bs ih => simp [List.foldl_cons, ih, h]

private theorem foldl_pair_second {A B : Type*} (l : List B) (f : A × ℕ → B → A × ℕ)
    (g : B → ℕ) (h : ∀ a b, (f a b).2 = a.2 + g b) (x : A × ℕ) :
    (l.foldl f x).2 = x.2 + (l.map g).sum := by
  induction l generalizing x with
  | nil => simp
  | cons b bs ih => simp [List.foldl_cons, ih, h, Nat.add_assoc]

theorem countedFold_erase {A : Type*} (ws : List ℕ) (p : ℕ)
    (step : A → List ℕ → A) (st : A × ℕ) :
    (countedFold ws p step st).1 = foldTuples ws p step st.1 := by
  induction ws generalizing p step st with
  | nil => by_cases h : p = 0 <;> simp [countedFold, foldTuples,h]
  | cons w ws ih =>
    by_cases h : p = 0
    · simp [countedFold, foldTuples,h]
    simp only [countedFold, foldTuples, h, if_false]
    exact foldl_pair_first _ _ _ (fun a b => ih _ _ a) _

theorem countedFold_visits {A : Type*} (ws : List ℕ) (p : ℕ)
    (step : A → List ℕ → A) (st : A × ℕ) :
    (countedFold ws p step st).2 = st.2 + prefixVisits ws p := by
  induction ws generalizing p step st with
  | nil => by_cases h : p = 0 <;> simp [countedFold, prefixVisits,h]
  | cons w ws ih =>
    by_cases h : p = 0
    · simp [countedFold, prefixVisits,h]
    simp only [countedFold, prefixVisits, h, if_false]
    rw [foldl_pair_second _ _ (fun b => prefixVisits ws (p-w*b)) (fun a b => ih _ _ a)]
    omega

private theorem sum_with_factor {A : Type*} (l : List A) (f g : A → ℕ) (k : ℕ)
    (h : ∀ a ∈ l, f a ≤ k * g a) :
    (l.map f).sum ≤ k * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    apply Nat.add_le_add (h a (by simp))
    exact ih (fun b hb => h b (by simp [hb]))

theorem prefixVisits_le (ws : List ℕ) (p : ℕ) (hw : ∀ w ∈ ws, 0 < w) :
    prefixVisits ws p ≤ (ws.length+1) * (tuples ws p).length := by
  induction ws generalizing p with
  | nil => by_cases hp : p = 0 <;> simp [prefixVisits, tuples, hp]
  | cons w ws ih =>
    by_cases hp : p = 0
    · simp [prefixVisits, tuples, hp]
    have ht : ∀ w ∈ ws, 0 < w := fun x hx => hw x (by simp [hx])
    have hb : 0 < (tuples (w::ws) p).length := by
      apply List.length_pos_of_mem (a := List.replicate (w::ws).length 0)
      apply (mem_tuples hw).2
      refine ⟨by simp, ?_⟩
      have hrep (l : List ℕ) : weightSum l (List.replicate l.length 0) = 0 := by
        induction l with
        | nil => rfl
        | cons r l ih => simp [weightSum, List.replicate_succ, ih]
      rw [hrep]
      omega
    have h := sum_with_factor (List.range ((p-1)/w+1))
      (fun b => prefixVisits ws (p-w*b)) (fun b => (tuples ws (p-w*b)).length)
      (ws.length+1) (fun b _ => ih _ ht)
    have he : (tuples (w::ws) p).length =
        ((List.range ((p-1)/w+1)).map (fun b => (tuples ws (p-w*b)).length)).sum := by
      simp [tuples, hp, List.length_flatMap]
    rw [← he] at h
    simp only [prefixVisits, hp, if_false, List.length_cons]
    rw [show ws.length + 1 + 1 = 1 + (ws.length+1) by omega, Nat.add_mul]
    omega

/-- Natural state data of a recursive call. Choose node-specific modes
    by the same finite packet interface used at the original root. -/
structure CallSchedule where
  M : ℕ
  a : ℕ
  L : ℕ
  u : ℕ
  p : ℕ
  B : ℤ → Type
  finiteB : ∀ t, Fintype (B t)

attribute [instance] CallSchedule.finiteB

noncomputable def CallSchedule.addresses (H : ℕ) (c : CallSchedule) : List (Slot × Fin 64) :=
  if c.M ≤ H then [] else
    (rootSlots c.u c.M c.L c.a c.p c.B).flatMap fun slot =>
      (List.finRange 64).map fun g => (slot,g)

theorem address_length (H : ℕ) (c : CallSchedule) (h : H < c.M) :
    (c.addresses H).length = (rootSlots c.u c.M c.L c.a c.p c.B).length * 64 := by
  simp only [CallSchedule.addresses, Nat.not_le_of_gt h, if_false, List.length_flatMap,
    List.length_map, List.length_finRange]
  simp

variable {A : Type*}

noncomputable def visitChildren (H : ℕ) (schedule : A → CallSchedule)
    (construct : A → Slot → Fin 64 → A) (c : A) : List A :=
  ((schedule c).addresses H).map fun p => construct c p.1 p.2

noncomputable def layer (H : ℕ) (schedule : A → CallSchedule)
    (construct : A → Slot → Fin 64 → A) (root : A) : ℕ → List A
  | 0 => [root]
  | d+1 => (layer H schedule construct root d).flatMap (visitChildren H schedule construct)

theorem layer_size_bound (H : ℕ) (schedule : A → CallSchedule)
    (construct : A → Slot → Fin 64 → A) (root : A)
    (shrink : ∀ c slot g, (slot,g) ∈ (schedule c).addresses H →
      8 * (schedule (construct c slot g)).M ≤ (schedule c).M) :
    ∀ d c, c ∈ layer H schedule construct root d → 8^d * (schedule c).M ≤ (schedule root).M := by
  intro d
  induction d with
  | zero =>
    intro c hc
    have he : c = root := by simpa [layer] using hc
    subst c
    simp
  | succ d ih =>
    intro c hc
    obtain ⟨parent,hparent,hchild⟩ := List.mem_flatMap.1 hc
    obtain ⟨⟨slot,g⟩,hm,he⟩ := List.mem_map.1 hchild
    subst c
    have hh := Nat.mul_le_mul_left (8^d) (shrink parent slot g hm)
    rw [pow_succ, Nat.mul_assoc]
    exact hh.trans (ih _ hparent)

#print axioms countedFold_erase
#print axioms countedFold_visits
#print axioms prefixVisits_le
#print axioms address_length
#print axioms layer_size_bound

end S11

