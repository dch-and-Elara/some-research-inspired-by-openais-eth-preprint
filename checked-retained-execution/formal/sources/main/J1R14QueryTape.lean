import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-! A literal fixed-width address for the source MAIN loop, not a handle
containing a precomputed fibre or a precomputed rational jet. Indices of the
source interval [-D,D] are stored with bias D; the source only prescribes a
logarithmic integral representation size, not this particular wire format. -/
namespace J1R14Query

abbrev Box (D : ℕ) := Fin (2*D+1)

def boxValue {D : ℕ} (b : Box D) : ℤ := (b.val : ℤ) - D

theorem boxValue_bounds {D : ℕ} (b : Box D) :
    -(D:ℤ) ≤ boxValue b ∧ boxValue b ≤ D := by
  have h := b.isLt
  unfold boxValue
  omega

def boxCode (D : ℕ) (y : ℤ) (lo : -(D:ℤ) ≤ y) (hi : y ≤ D) : Box D :=
  ⟨(y + D).toNat, by omega⟩

theorem boxValue_code (D : ℕ) (y : ℤ) (lo : -(D:ℤ) ≤ y) (hi : y ≤ D) :
    boxValue (boxCode D y lo hi) = y := by
  have hn : 0 ≤ y + (D:ℤ) := by omega
  simp [boxValue,boxCode,Int.toNat_of_nonneg hn]

theorem boxCode_value {D : ℕ} (b : Box D) :
    boxCode D (boxValue b) (boxValue_bounds b).1 (boxValue_bounds b).2 = b := by
  apply Fin.ext
  simp [boxValue,boxCode]

/-- A little-endian fixed-width word. The tape physically has one entry for
each bit, including leading zeroes. -/
def word (w v : ℕ) : List Bool := List.ofFn fun i : Fin w => v.testBit i.val

@[simp] theorem word_length (w v : ℕ) : (word w v).length = w := by simp [word]

theorem word_value_injective {w x y : ℕ} (hx : x < 2^w) (hy : y < 2^w)
    (h : word w x = word w y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · have hj : i < (word w x).length := by simpa using hi
    simpa [word] using List.getElem_of_eq h hj
  · have hw : w ≤ i := by omega
    have hp : 2^w ≤ (2:ℕ)^i := Nat.pow_le_pow_right (by decide) hw
    rw [Nat.testBit_lt_two_pow (hx.trans_le hp),Nat.testBit_lt_two_pow (hy.trans_le hp)]

def finWord {m : ℕ} (x : Fin m) : List Bool := word (Nat.clog 2 m) x.val

@[simp] theorem finWord_length {m : ℕ} (x : Fin m) :
    (finWord x).length = Nat.clog 2 m := by simp [finWord]

theorem finWord_injective (m : ℕ) : Function.Injective (@finWord m) := by
  intro x y h
  have hp := Nat.le_pow_clog (b:=2) (by decide) m
  exact Fin.ext (word_value_injective (x.isLt.trans_le hp) (y.isLt.trans_le hp) h)

def mask {n : ℕ} (E : Finset (Fin n)) : List Bool :=
  List.ofFn (fun j : Fin n => decide (j ∈ E))

@[simp] theorem mask_length {n : ℕ} (E : Finset (Fin n)) :
    (mask E).length = n := by simp [mask]

theorem mask_injective (n : ℕ) : Function.Injective (@mask n) := by
  intro x y h
  ext j
  have hj : j.val < (mask x).length := by simp
  have e : decide (j ∈ x) = decide (j ∈ y) := by
    simpa [mask] using List.getElem_of_eq h hj
  constructor
  · intro hmem
    have hx : decide (j ∈ x) = true := decide_eq_true hmem
    exact of_decide_eq_true (e.symm.trans hx)
  · intro hmem
    have hy : decide (j ∈ y) = true := decide_eq_true hmem
    exact of_decide_eq_true (e.trans hy)

theorem flatMap_length_const {A B : Type*} (enc : A → List B) (w : ℕ)
    (hlen : ∀ a, (enc a).length = w) (xs : List A) :
    (xs.flatMap enc).length = xs.length * w := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.length_append,hlen,ih,List.length_cons,Nat.succ_mul]
    omega

theorem flatMap_fixed_injective {A B : Type*} (enc : A → List B) (w : ℕ)
    (hlen : ∀ a, (enc a).length = w) (hinj : Function.Injective enc)
    {xs ys : List A} (hcard : xs.length = ys.length) (he : xs.flatMap enc = ys.flatMap enc) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hcard.symm
  | cons a xs ih =>
    cases ys with
    | nil => simp at hcard
    | cons b ys =>
      simp only [List.length_cons,Nat.succ.injEq] at hcard
      simp only [List.flatMap_cons] at he
      obtain ⟨h₁,h₂⟩ := List.append_inj he (by rw [hlen,hlen])
      rw [hinj h₁,ih hcard h₂]

def boxTape {D m : ℕ} (y : Fin m → Box D) : List Bool :=
  (List.ofFn y).flatMap finWord

@[simp] theorem boxTape_length {D m : ℕ} (y : Fin m → Box D) :
    (boxTape y).length = m * Nat.clog 2 (2*D+1) := by
  simp only [boxTape]
  rw [flatMap_length_const finWord (Nat.clog 2 (2*D+1)) finWord_length,List.length_ofFn]

theorem boxTape_injective (D m : ℕ) : Function.Injective (@boxTape D m) := by
  intro x y h
  have e : List.ofFn x = List.ofFn y := flatMap_fixed_injective finWord _ finWord_length
    (finWord_injective _) (by simp) h
  funext j
  have hj : j.val < (List.ofFn x).length := by simp
  simpa using List.getElem_of_eq e hj

@[ext] structure Address (Q n m D q : ℕ) where
  t : Fin Q
  E : Finset (Fin n)
  U : Finset (Fin n)
  y : Fin m → Box D
  subset : U ⊆ E
  order : E.card ≤ q

def tape {Q n m D q : ℕ} (a : Address Q n m D q) : List Bool :=
  finWord a.t ++ mask a.E ++ mask a.U ++ boxTape a.y

def rootWidth (Q n m D : ℕ) : ℕ := Nat.clog 2 Q + 2*n + m*Nat.clog 2 (2*D+1)

theorem tape_length {Q n m D q : ℕ} (a : Address Q n m D q) :
    (tape a).length = rootWidth Q n m D := by
  simp only [tape,rootWidth,List.length_append,finWord_length,mask_length,boxTape_length]
  omega

theorem tape_injective (Q n m D q : ℕ) : Function.Injective (@tape Q n m D q) := by
  intro a b h
  unfold tape at h
  obtain ⟨h₁,hy⟩ := List.append_inj h (by simp)
  obtain ⟨h₂,hU⟩ := List.append_inj h₁ (by simp)
  obtain ⟨ht,hE⟩ := List.append_inj h₂ (by simp)
  exact Address.ext (finWord_injective _ ht) (mask_injective _ hE)
    (mask_injective _ hU) (boxTape_injective _ _ hy)

def groupTape {Q n m D q r : ℕ} (a : Address Q n m D q) (g : Fin r) : List Bool :=
  tape a ++ finWord g

theorem groupTape_length {Q n m D q r : ℕ} (a : Address Q n m D q) (g : Fin r) :
    (groupTape a g).length = rootWidth Q n m D + Nat.clog 2 r := by
  simp [groupTape,tape_length]

/-- A one-bit-per-write interface necessarily charges exactly this many bit
writes to emit each address with this serialization. This statement is not
a cost claim about the source reply or generating the original matrices. -/
theorem emitted_bits {Q n m D q : ℕ} (xs : List (Address Q n m D q)) :
    (xs.flatMap tape).length = xs.length * rootWidth Q n m D :=
  flatMap_length_const tape _ tape_length xs

#print axioms boxValue_bounds
#print axioms boxValue_code
#print axioms boxCode_value
#print axioms word_value_injective
#print axioms finWord_injective
#print axioms mask_injective
#print axioms flatMap_fixed_injective
#print axioms boxTape_length
#print axioms tape_length
#print axioms tape_injective
#print axioms groupTape_length
#print axioms emitted_bits
end J1R14Query
