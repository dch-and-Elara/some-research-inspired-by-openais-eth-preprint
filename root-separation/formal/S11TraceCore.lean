
import S11DFSWork

namespace S11

/-- Fixed-width bit addition used on one coordinate of a modular sum.
    Each recursive stage computes and writes one output digit. -/
def addWord : ℕ → ℕ → ℕ → Bool → ℕ × ℕ
  | 0, _, _, _ => (0,0)
  | p+1, x, y, c =>
    let digit := x%2 + y%2 + c.toNat
    let rest := addWord p (x/2) (y/2) (decide (2 ≤ digit))
    ((digit%2) + 2*rest.1, rest.2+1)

theorem addWord_count (p x y : ℕ) (c : Bool) :
    (addWord p x y c).2 = p := by
  induction p generalizing x y c with
  | zero => rfl
  | succ p ih => simp [addWord, ih]

private theorem mod_twice (e h q : ℕ) (he : e < 2) (hq : 0 < q) :
    (e+2*h)%(2*q) = e+2*(h%q) := by
  have hh := Nat.mod_add_div h q
  conv_lhs => rw [← hh]
  rw [Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by have hm := Nat.mod_lt h hq; omega)

theorem addWord_value (p x y : ℕ) (c : Bool) :
    (addWord p x y c).1 = (x+y+c.toNat) % 2^p := by
  induction p generalizing x y c with
  | zero => simp [addWord, Nat.mod_one]
  | succ p ih =>
    let z := x%2+y%2+c.toNat
    let carry : Bool := decide (2≤z)
    have hz : z < 4 := by
      have hc : c.toNat ≤ 1 := by cases c <;> decide
      have hx := Nat.mod_lt x (by decide : 0<2)
      have hy := Nat.mod_lt y (by decide : 0<2)
      unfold z
      omega
    have hcarry : carry.toNat = z/2 := by
      by_cases h : 2≤z
      · simp [carry,h]; omega
      · simp [carry,h]; omega
    have he : x+y+c.toNat = z%2 + 2*(x/2+y/2+carry.toNat) := by
      have hx := Nat.mod_add_div x 2
      have hy := Nat.mod_add_div y 2
      have h' := Nat.mod_add_div z 2
      unfold z at h'
      dsimp [z]
      omega
    change z%2 + 2 * (addWord p (x/2) (y/2) carry).1 = _
    rw [ih, he, pow_succ, Nat.mul_comm (2^p), mod_twice _ _ _ (Nat.mod_lt _ (by decide)) (by positivity)]

section Trace
variable {R : ℤ → Type*} [∀ t, CommSemiring (R t)]

theorem sourceTrace_covers (u M L a p : ℕ) (B : ℤ → Type*) [∀ t, Fintype (B t)]
    (child : (t : ℤ) → ℕ → List ℕ → Fin 64 → R t)
    {t : ℤ} (ht : t ∈ centers u L) {j : ℕ} (hj : j < probeCount M L)
    (β : List ℕ) (hβ : β ∈ tuples
      (modeWeights (B t) (level t) (precision p M a u L t)) (precision p M a u L t)) :
    Slot.mk t j β ∈ sourceTrace B M L a u p child := by
  rw [sourceTrace_eq_slots,rootSlots]
  apply List.mem_flatMap.2
  refine ⟨t,Finset.mem_toList.2 ht,List.mem_flatMap.2 ⟨j,List.mem_range.2 hj,?_⟩⟩
  exact List.mem_map.2 ⟨β,hβ,rfl⟩

theorem sourceTrace_mem_iff (u M L a p : ℕ) (B : ℤ → Type*) [∀ t, Fintype (B t)]
    (child : (t : ℤ) → ℕ → List ℕ → Fin 64 → R t) (t : ℤ) (j : ℕ) (β : List ℕ) :
    Slot.mk t j β ∈ sourceTrace B M L a u p child ↔
      t ∈ centers u L ∧ j < probeCount M L ∧
      β.length = (modeWeights (B t) (level t) (precision p M a u L t)).length ∧
      weightSum (modeWeights (B t) (level t) (precision p M a u L t)) β < precision p M a u L t := by
  have hw : ∀ w ∈ modeWeights (B t) (level t) (precision p M a u L t), 0 < w := by
    intro w h
    obtain ⟨m,_,rfl⟩ := List.mem_map.1 h
    omega
  constructor
  · rw [sourceTrace_eq_slots, rootSlots]
    intro h
    obtain ⟨t',ht,h⟩ := List.mem_flatMap.1 h
    obtain ⟨j',hj,hj'⟩ := List.mem_flatMap.1 h
    obtain ⟨β',hβ,he⟩ := List.mem_map.1 hj'
    cases he
    exact ⟨Finset.mem_toList.1 ht, List.mem_range.1 hj, (mem_tuples hw).1 hβ⟩
  · rintro ⟨ht,hj,hb,hp⟩
    exact sourceTrace_covers u M L a p B child ht hj β ((mem_tuples hw).2 ⟨hb,hp⟩)

/-- One fixed-width coordinate is sufficient for a lower charge. The other
    coordinates, child work, and interpolation are outside this counter. -/
noncomputable def accumulatorBitWork (p M a u L : ℕ) (trace : List Slot)
    (acc term : Slot → ℕ) : ℕ :=
  (trace.map fun s => (addWord (precision p M a u L s.center) (acc s) (term s) false).2).sum

theorem accumulatorBitWork_ge (p M a u L : ℕ) (hp : 0 < p)
    (trace : List Slot) (acc term : Slot → ℕ) :
    trace.length ≤ accumulatorBitWork p M a u L trace acc term := by
  apply slot_charge
  intro s _
  rw [addWord_count]
  unfold precision
  omega

variable {W P : Type*} [Fintype W] [Fintype P]

/-- Shared bridge. Applied to either graph reduction, all visited slots
    come from the actual accumulator, and its bit charge is strictly
    positive for every slot, even when the product is zero. -/
theorem literal_root_bits {M a L u p : ℕ} (G : Packing W P a L)
    (hwire : Fintype.card W = M) (Δ : ℚ)
    (cert : SourceDensity.CollisionCertificate G.cell Δ)
    (hpack : Fintype.card P * L ≤ 3*M)
    (hM : 0 < M) (hu : 0 < u) (ha : a = 2*u) (hL : L = 2^a) (hp : 0 < p)
    (child : (t : ℤ) → ℕ → List ℕ → Fin 64 → R t) (acc term : Slot → ℕ) :
    let d := Fintype.card (G.mixedAt 1) * lowWeights u L
    M ≤ 4 * (Nat.sqrt u + 1) * d ∧
    2^d ≤ accumulatorBitWork p M a u L (sourceTrace G.mixedAt M L a u p child) acc term := by
  obtain ⟨hsize,hslots⟩ := odd_root_lower (p := p) G hwire Δ cert hpack hM hu ha hL
  refine ⟨hsize, hslots.trans ?_⟩
  rw [← sourceTrace_eq_slots G.mixedAt M L a u p child]
  exact accumulatorBitWork_ge p M a u L hp _ acc term

end Trace

#print axioms addWord_count
#print axioms addWord_value
#print axioms sourceTrace_covers
#print axioms sourceTrace_mem_iff
#print axioms accumulatorBitWork_ge
#print axioms literal_root_bits

end S11

