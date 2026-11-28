import J1R14QueryBasis
import A1R10Word

/-! Bit-costed scalar accumulation of a single printed MAIN measurement
row once its signed-unit tokens have arrived. The copied-coordinate test
for each slot is the exact source test; generating/locating these tokens is
not treated as a free part of the theorem below. -/
namespace J1R14Query
open AOracleMachineTime A1R10
open scoped BigOperators

inductive SignedUnit where
  | zero | plus | minus

def SignedUnit.amount : SignedUnit → ℤ
  | .zero => 0
  | .plus => 1
  | .minus => -1

def signedUnit (j : ℤ) : SignedUnit :=
  if j = 0 then .zero else if j = 1 then .plus else .minus

theorem signedUnit_exact (j : ℤ) (h : j=0 ∨ j=1 ∨ j = -1) :
    (signedUnit j).amount = j := by
  rcases h with rfl | rfl | rfl <;> decide


/-- The event tape carries one two-bit token for each inspected copied
slot: zero, +1 or -1. This is an explicit local format, not the original
input CNF or a free full-row answer. -/
def SignedUnit.bits : SignedUnit → List Bool
  | .zero => [false,false]
  | .plus => [false,true]
  | .minus => [true,false]

theorem SignedUnit.bits_length (t : SignedUnit) : t.bits.length = 2 := by
  cases t <;> rfl

theorem SignedUnit.bits_injective : Function.Injective SignedUnit.bits := by
  intro x y h
  cases x <;> cases y <;> simp_all [SignedUnit.bits]

def rowStep {p : ℕ} (hp : 0<p) (a : Word p) : SignedUnit → Meter (Word p)
  | .zero => ⟨a,0⟩
  | .plus => addWord a (wordOne p)
  | .minus => subWord hp a (wordOne p)

theorem rowStep_read {p : ℕ} (hp : 0<p) (a : Word p) (t : SignedUnit) :
    wordRead (rowStep hp a t).result = wordRead a + (t.amount : ZMod (2^p)) := by
  cases t with
  | zero => simp [rowStep,SignedUnit.amount]
  | plus => simp [rowStep,SignedUnit.amount,addWord_read,wordOne_read p hp]
  | minus => simp [rowStep,SignedUnit.amount,subWord_read,wordOne_read p hp,sub_eq_add_neg]

theorem rowStep_cost {p : ℕ} (hp : 0<p) (a : Word p) (t : SignedUnit) :
    (rowStep hp a t).steps ≤ 32*(p+1)^2 := by
  cases t with
  | zero => exact Nat.zero_le _
  | plus => exact (wordOps p hp).add_cost a (wordOne p)
  | minus => exact (wordOps p hp).sub_cost a (wordOne p)

def measureTape {p : ℕ} (hp : 0<p) (a : Word p) : List SignedUnit → Meter (Word p)
  | [] => ⟨a,0⟩
  | t :: ts =>
    let first := rowStep hp a t
    let rest := measureTape hp first.result ts
    ⟨rest.result, t.bits.length + first.steps + rest.steps⟩

theorem measureTape_read {p : ℕ} (hp : 0<p) (a : Word p) (ts : List SignedUnit) :
    wordRead (measureTape hp a ts).result =
      wordRead a + ((ts.map SignedUnit.amount).sum : ZMod (2^p)) := by
  induction ts generalizing a with
  | nil => simp [measureTape]
  | cons t ts ih =>
    change wordRead (measureTape hp (rowStep hp a t).result ts).result =
      wordRead a + (((t::ts).map SignedUnit.amount).sum : ZMod (2^p))
    rw [ih,rowStep_read,List.map_cons,List.sum_cons,Int.cast_add,add_assoc]

theorem measureTape_cost {p : ℕ} (hp : 0<p) (a : Word p) (ts : List SignedUnit) :
    (measureTape hp a ts).steps ≤ ts.length*(2+32*(p+1)^2) := by
  induction ts generalizing a with
  | nil => simp [measureTape]
  | cons t ts ih =>
    have h₁ := rowStep_cost hp a t
    have h₂ := ih (rowStep hp a t).result
    change t.bits.length+(rowStep hp a t).steps+(measureTape hp (rowStep hp a t).result ts).steps ≤ _
    rw [SignedUnit.bits_length,List.length_cons,Nat.succ_mul]
    omega

universe u v w c b
variable {I : Type u} {S : Type v} {X : Type w} {Copy : Type c} {Pin : Type b}
variable [Fintype I] [DecidableEq I] [Fintype S] [LinearOrder S]

variable (L : MainProbe.DiagonalLayout I S X Copy Pin)
variable (interval : Finset ℕ) (hz : 0 ∉ interval)

def slotAmount (t : I) (g : S) (h : Copy × Exceptional I S interval) (x : X → Bool)
    (u : MainProbe.Cell I S) : ℤ :=
  (printedBasis L interval hz).entry h.2 u * (L.occupied h.1 u).elim 0 (groupBit L t g x)

omit [DecidableEq I] [Fintype S] in
theorem slotAmount_signed (t : I) (g : S) (h : Copy × Exceptional I S interval) (x : X → Bool)
    (u : MainProbe.Cell I S) :
    slotAmount L interval hz t g h x u = 0 ∨ slotAmount L interval hz t g h x u = 1 ∨
      slotAmount L interval hz t g h x u = -1 := by
  unfold slotAmount
  cases hx : L.occupied h.1 u with
  | none => simp
  | some v =>
    by_cases hv : L.variableWord v t = g ∧ x v = true
    · simpa [groupBit,hv] using printedBasis_signed L interval hz h.2 u
    · simp [groupBit,hv]

def actualTokens {d : ℕ} (e : Fin d ≃ MainProbe.Cell I S)
    (t : I) (g : S) (h : Copy × Exceptional I S interval) (x : X → Bool) : List SignedUnit :=
  List.ofFn fun j => signedUnit (slotAmount L interval hz t g h x (e j))

theorem actualTokens_sum {d : ℕ} (e : Fin d ≃ MainProbe.Cell I S)
    (t : I) (g : S) (h : Copy × Exceptional I S interval) (x : X → Bool) :
    ((actualTokens L interval hz e t g h x).map SignedUnit.amount).sum =
      rowRead L (printedBasis L interval hz) t g h x := by
  unfold actualTokens
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply]
  calc
    _ = ∑ i, slotAmount L interval hz t g h x (e i) :=
      Finset.sum_congr rfl fun i _ =>
        signedUnit_exact _ (slotAmount_signed L interval hz t g h x (e i))
    _ = _ := Equiv.sum_comp e (slotAmount L interval hz t g h x)

theorem actual_measure_tape {p d : ℕ} (hp : 0<p) (a : Word p) (e : Fin d ≃ MainProbe.Cell I S)
    (t : I) (g : S) (h : Copy × Exceptional I S interval) (x : X → Bool) :
    let out := measureTape hp a (actualTokens L interval hz e t g h x)
    wordRead out.result =
      wordRead a + (rowRead L (printedBasis L interval hz) t g h x : ZMod (2^p)) ∧
    out.steps ≤ d*(2+32*(p+1)^2) := by
  dsimp
  refine ⟨?_,?_⟩
  · rw [measureTape_read,actualTokens_sum]
  · exact (measureTape_cost hp a _).trans_eq (by simp [actualTokens])


/-- No aliasing of legal signed values occurs in a register wider than
the diameter of the printed measurement interval. -/
theorem signed_cast_equal_iff {D p : ℕ} (hwide : 2*D < 2^p) (x y : ℤ)
    (hx : -(D:ℤ) ≤ x ∧ x ≤ D) (hy : -(D:ℤ) ≤ y ∧ y ≤ D) :
    (x : ZMod (2^p)) = (y : ZMod (2^p)) ↔ x = y := by
  constructor
  · intro h
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub x y (2^p)).mp h
    have hb : (y-x).natAbs < 2^p := by omega
    have hz : y-x=0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hb)
    omega
  · rintro rfl
    rfl

theorem actual_row_comparison {p d : ℕ} (hp : 0<p) (a : Word p)
    (e : Fin d ≃ MainProbe.Cell I S)
    (hwide : 2 * Fintype.card (MainProbe.Cell I S) < 2^p)
    (t : I) (g : S) (h : Copy × Exceptional I S interval) (x : X → Bool)
    (y : Box (Fintype.card (MainProbe.Cell I S))) :
    wordRead (measureTape hp a (actualTokens L interval hz e t g h x)).result =
      wordRead a + (boxValue y : ZMod (2^p)) ↔
      rowRead L (printedBasis L interval hz) t g h x = boxValue y := by
  rw [(actual_measure_tape L interval hz hp a e t g h x).1]
  constructor
  · intro he
    exact (signed_cast_equal_iff hwide _ _
      (printed_read_bounds L interval hz t g h x) (boxValue_bounds y)).mp (add_left_cancel he)
  · intro he
    rw [he]


theorem enough_measure_bits (D : ℕ) :
    0 < Nat.clog 2 (2*D+1)+1 ∧ 2*D < 2^(Nat.clog 2 (2*D+1)+1) := by
  refine ⟨by omega,?_⟩
  have hb := Nat.le_pow_clog (b:=2) (by decide) (2*D+1)
  rw [pow_succ]
  omega

#print axioms SignedUnit.bits_length
#print axioms SignedUnit.bits_injective
#print axioms enough_measure_bits
#print axioms signed_cast_equal_iff
#print axioms actual_row_comparison
#print axioms signedUnit_exact
#print axioms rowStep_read
#print axioms rowStep_cost
#print axioms measureTape_read
#print axioms measureTape_cost
#print axioms slotAmount_signed
#print axioms actualTokens_sum
#print axioms actual_measure_tape
end J1R14Query
