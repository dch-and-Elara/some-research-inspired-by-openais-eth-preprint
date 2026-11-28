
import J9R19CompiledBitsLocal

/-! Charged arithmetic for the original public binomial kernel and
for powers of real integer ordinals/denominators. These are explicit
executables, not calls to arbitrary arithmetic circuits. -/
namespace J9R19CompiledBits
open scoped BigOperators
set_option linter.unusedSectionVars false

structure PowerRun where
  value : ℤ
  writes : List ℤ
  work : ℕ

def powerRun (a : ℤ) : ℕ→PowerRun
  | 0 => ⟨1,[1],0⟩
  | n+1 =>
    let s := powerRun a n
    let p := s.value*a
    ⟨p,p::s.writes,s.work+1⟩

theorem powerRun_exact (a : ℤ) (n : ℕ) :
    (powerRun a n).value=a^n ∧ (powerRun a n).work=n := by
  induction n with
  | zero => simp [powerRun]
  | succ n ih => simp [powerRun,pow_succ,ih.1,ih.2]

theorem powerRun_width {b : ℕ} (a : ℤ) (h : Fits b a) (n : ℕ) :
    ∀ x∈(powerRun a n).writes, Fits (b*n) x := by
  induction n with
  | zero => simpa [powerRun] using Fits.one 0
  | succ n ih =>
    intro x hx
    simp only [powerRun,List.mem_cons] at hx
    rcases hx with rfl|hx
    · rw [(powerRun_exact _ _).1,Nat.mul_succ]
      exact (h.pow n).mul h
    · exact (ih x hx).mono (Nat.mul_le_mul_left _ (by omega))

/-- Add adjacent entries of the old Pascal row. Each old slot is read
once, and the final edge copies the old last slot. -/
def passport (previous : ℕ) : List ℕ → List ℕ
  | [] => [previous]
  | a::as => (previous+a)::passport a as

theorem passport_length (p : ℕ) (xs : List ℕ) :
    (passport p xs).length=xs.length+1 := by
  induction xs generalizing p with
  | nil => rfl
  | cons a as ih => simp only [passport,List.length_cons,ih]

theorem passport_get (p : ℕ) (xs : List ℕ) (i : ℕ) :
    ((passport p xs)[i]?).getD 0 =
      (if i=0 then p else (xs[i-1]?).getD 0) + (xs[i]?).getD 0 := by
  induction xs generalizing p i with
  | nil =>
    cases i with
    | zero => simp [passport]
    | succ i => simp [passport]
  | cons a as ih =>
    cases i with
    | zero => simp [passport]
    | succ i =>
      change ((passport a as)[i]?).getD 0 = _
      rw [ih]
      cases i <;> simp

structure PascalRun where
  row : List ℕ
  writes : List ℕ
  work : ℕ

def pascalRun : ℕ → PascalRun
  | 0 => ⟨[1],[1],0⟩
  | n+1 =>
    let p := pascalRun n
    let r := passport 0 p.row
    ⟨r,p.writes++r,p.work+p.row.length⟩

theorem pascalRun_exact (n : ℕ) :
    (pascalRun n).row.length=n+1 ∧ ∀ i, ((pascalRun n).row[i]?).getD 0 = n.choose i := by
  induction n with
  | zero =>
    constructor
    · rfl
    · intro i; cases i <;> simp [pascalRun]
  | succ n ih =>
    constructor
    · simp only [pascalRun,passport_length,ih.1]
    · intro i
      simp only [pascalRun,passport_get]
      cases i with
      | zero => simp [ih.2]
      | succ i => simp [ih.2,Nat.choose_succ_succ]

theorem pascalRun_work (n : ℕ) : (pascalRun n).work ≤ n*(n+1) := by
  induction n with
  | zero => simp [pascalRun]
  | succ n ih =>
    simp only [pascalRun,(pascalRun_exact n).1]
    calc
      _ ≤ n*(n+1)+(n+1) := Nat.add_le_add_right ih _
      _ ≤ _ := by
        rw [show n*(n+1)+(n+1)=(n+1)*(n+1) by ring]
        exact Nat.mul_le_mul_left _ (by omega)

theorem passport_width (xs : List ℕ) (p b : ℕ) (hp : p≤2^b)
    (hx : ∀ x∈xs, x≤2^b) : ∀ y∈passport p xs,y≤2^(b+1) := by
  induction xs generalizing p with
  | nil =>
    intro y hy
    simp only [passport,List.mem_singleton] at hy
    subst y
    exact hp.trans (Nat.pow_le_pow_right (by omega) (by omega))
  | cons a as ih =>
    intro y hy
    have ha := hx a (by simp)
    simp only [passport,List.mem_cons] at hy
    rcases hy with rfl|hy
    · rw [pow_succ]; omega
    · exact ih a ha (fun x hx' => hx x (by simp [hx'])) y hy

theorem pascalRun_width (n : ℕ) :
    (∀ x∈(pascalRun n).row, x≤2^n) ∧ (∀ x∈(pascalRun n).writes, x≤2^n) := by
  induction n with
  | zero => simp [pascalRun]
  | succ n ih =>
    have h := passport_width (pascalRun n).row 0 n (Nat.zero_le _) ih.1
    refine ⟨h,?_⟩
    intro x hx
    simp only [pascalRun,List.mem_append] at hx
    rcases hx with hx|hx
    · exact (ih.2 x hx).trans (Nat.pow_le_pow_right (by omega) (by omega))
    · exact h x hx

structure KernelRun where
  coeff : ℤ
  oldRows : List ℕ
  work : ℕ

def kernelRun (L : ℕ) : KernelRun :=
  let p := pascalRun (2*L-1)
  ⟨-((p.row[L]?.getD 0 : ℕ) : ℤ),p.writes,p.work+1⟩

theorem kernelRun_exact (L : ℕ) : (kernelRun L).coeff=J9FactorBounds.kernel L := by
  simp only [kernelRun,J9FactorBounds.kernel,(pascalRun_exact _).2]

theorem kernelRun_work (L : ℕ) :
    (kernelRun L).work≤(2*L-1)*(2*L)+1 := by
  have h := pascalRun_work (2*L-1)
  change (pascalRun (2*L-1)).work+1≤_
  by_cases hL : 0<L
  · rw [show 2*L-1+1=2*L by omega] at h
    exact Nat.add_le_add_right h 1
  · have eq : L=0 := by omega
    subst L
    decide

theorem kernelRun_width (L : ℕ) (hL : 1≤L) :
    Fits (2*L) (kernelRun L).coeff ∧ (∀ z∈(kernelRun L).oldRows,z≤2^(2*L)) := by
  refine ⟨kernelRun_exact L ▸ ?_,?_⟩
  · exact kernel_fits L hL
  · intro z hz
    exact ((pascalRun_width _).2 z hz).trans (Nat.pow_le_pow_right (by omega) (by omega))

#print axioms powerRun_exact
#print axioms powerRun_width
#print axioms pascalRun_exact
#print axioms pascalRun_work
#print axioms pascalRun_width
#print axioms kernelRun_exact
#print axioms kernelRun_work
#print axioms kernelRun_width
end J9R19CompiledBits
