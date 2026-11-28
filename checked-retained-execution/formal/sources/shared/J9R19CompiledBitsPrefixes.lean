
import J9R18CompiledSmallScope

/-! Signed word-magnitude certificates and an actual two-pass product
evaluator. An index-exclusion product never divides by a vertex mass,
including at zero. The machine count is the number of integer multiplications. -/
namespace J9R19CompiledBits
open scoped BigOperators
set_option linter.unusedSectionVars false

/-- Inclusive unsigned magnitude bound. It fits in w+1 magnitude digits,
or w+2 digits including a sign bit. -/
def Fits (w : ℕ) (x : ℤ) : Prop := x.natAbs ≤ 2^w

theorem Fits.signedWidth {w : ℕ} {x : ℤ} (h : Fits w x) :
    x.natAbs < 2^(w+1) := by
  have h0 : 0 < 2^w := by positivity
  rw [pow_succ]
  exact lt_of_le_of_lt h (by omega)

theorem Fits.mono {w w' : ℕ} {x : ℤ} (h : Fits w x) (le : w≤w') :
    Fits w' x := h.trans (Nat.pow_le_pow_right (by omega) le)

theorem Fits.zero (w : ℕ) : Fits w 0 := by simp [Fits]

theorem Fits.one (w : ℕ) : Fits w 1 := by
  unfold Fits
  have h : 0 < 2^w := by positivity
  simp only [Int.natAbs_one]
  exact h

theorem Fits.neg {w : ℕ} {x : ℤ} (h : Fits w x) : Fits w (-x) := by
  simpa only [Fits,Int.natAbs_neg] using h

theorem Fits.mul {u v : ℕ} {x y : ℤ} (hx : Fits u x) (hy : Fits v y) :
    Fits (u+v) (x*y) := by
  unfold Fits at *
  rw [Int.natAbs_mul,pow_add]
  exact Nat.mul_le_mul hx hy

theorem Fits.add {w : ℕ} {x y : ℤ} (hx : Fits w x) (hy : Fits w y) :
    Fits (w+1) (x+y) := by
  unfold Fits at *
  rw [pow_succ]
  exact (Int.natAbs_add_le x y).trans (by omega)

theorem Fits.sub {w : ℕ} {x y : ℤ} (hx : Fits w x) (hy : Fits w y) :
    Fits (w+1) (x-y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem product_fits {b : ℕ} (xs : List ℤ) (h : ∀ x∈xs, Fits b x) :
    Fits (b*xs.length) xs.prod := by
  induction xs with
  | nil => simpa using Fits.one 0
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun a ha => h a (by simp [ha]))
    have hh := hx.mul hxs
    simpa only [List.prod_cons,List.length_cons,Nat.mul_succ,Nat.add_comm] using hh

theorem sum_fits {b : ℕ} (xs : List ℤ) (h : ∀ x∈xs, Fits b x) :
    Fits (b+xs.length) xs.sum := by
  induction xs with
  | nil => simpa using Fits.zero b
  | cons x xs ih =>
    have hx : Fits (b+xs.length) x := (h x (by simp)).mono (Nat.le_add_right _ _)
    have hs := ih (fun a ha => h a (by simp [ha]))
    simpa only [List.sum_cons,List.length_cons,Nat.add_assoc] using hx.add hs

structure SuffixRun where
  whole : ℤ
  after : List ℤ
  work : ℕ

/-- A right-to-left pass. Each multiplication writes a stored tail
product once; neither multiplication nor an input is evaluated twice. -/
def suffixRun : List ℤ → SuffixRun
  | [] => ⟨1,[],0⟩
  | x::xs =>
    let q := suffixRun xs
    ⟨x*q.whole,q.whole::q.after,q.work+1⟩

def tailProducts : List ℤ → List ℤ
  | [] => []
  | _::xs => xs.prod::tailProducts xs

theorem suffixRun_exact (xs : List ℤ) :
    (suffixRun xs).whole=xs.prod ∧ (suffixRun xs).after=tailProducts xs ∧
      (suffixRun xs).work=xs.length := by
  induction xs with
  | nil => simp [suffixRun,tailProducts]
  | cons x xs ih => simp [suffixRun,tailProducts,ih.1,ih.2.1,ih.2.2]

theorem tailProducts_fits {b : ℕ} (xs : List ℤ) (h : ∀ x∈xs, Fits b x) :
    ∀ x∈tailProducts xs, Fits (b*xs.length) x := by
  induction xs with
  | nil => simp [tailProducts]
  | cons a xs ih =>
    have sub : ∀ x∈xs, Fits b x := fun x hx => h x (by simp [hx])
    intro x hx
    simp only [tailProducts,List.mem_cons] at hx
    have h0 : Fits (b*xs.length) x := by
      rcases hx with rfl | hx
      · exact product_fits xs sub
      · exact ih sub x hx
    exact h0.mono (Nat.mul_le_mul_left _ (by simp))

structure PrefixRun where
  excluded : List ℤ
  prefixCells : List ℤ
  work : ℕ

/-- A left-to-right pass with the actual suffix tape as a second input.
One multiplication emits an exclusion product; one updates the prefix. -/
def prefixRun (p : ℤ) : List ℤ → List ℤ → PrefixRun
  | x::xs, s::ss =>
    let q := prefixRun (p*x) xs ss
    ⟨(p*s)::q.excluded,p::q.prefixCells,q.work+2⟩
  | _, _ => ⟨[],[p],0⟩

def omitProduct (p : ℤ) : List ℤ → List ℤ
  | [] => []
  | x::xs => (p*xs.prod)::omitProduct (p*x) xs

theorem prefixRun_exact (xs : List ℤ) (p : ℤ) :
    (prefixRun p xs (tailProducts xs)).excluded=omitProduct p xs ∧
      (prefixRun p xs (tailProducts xs)).work=2*xs.length := by
  induction xs generalizing p with
  | nil => simp [prefixRun,omitProduct]
  | cons x xs ih =>
    simp [prefixRun,omitProduct,tailProducts,(ih (p*x)).1,(ih (p*x)).2,Nat.mul_succ]

/-- All integer values *written* by the left pass, including the final
unused prefix for its uniform loop shape, satisfy a common bit budget. -/
theorem prefixRun_fits {b e : ℕ} (xs : List ℤ) (p : ℤ)
    (hp : Fits e p) (h : ∀ x∈xs, Fits b x) :
    ∀ z∈(prefixRun p xs (tailProducts xs)).excluded ++
      (prefixRun p xs (tailProducts xs)).prefixCells, Fits (e+b*xs.length) z := by
  induction xs generalizing p e with
  | nil =>
    intro z hz
    simp [prefixRun] at hz
    simpa [← hz] using hp
  | cons x xs ih =>
    have hx : Fits b x := h x (by simp)
    have sub : ∀ a∈xs, Fits b a := fun a ha => h a (by simp [ha])
    have step := ih (p*x) (hp.mul hx) sub
    intro z hz
    simp only [tailProducts,prefixRun,List.mem_append,List.mem_cons] at hz
    have key : e+b*(x::xs).length=(e+b)+b*xs.length := by
      simp only [List.length_cons,Nat.mul_succ]
      omega
    rw [key]
    rcases hz with (h0 | h0) | (h0 | h0)
    · subst z
      exact (hp.mul (product_fits xs sub)).mono (by omega)
    · exact step z (List.mem_append.mpr (Or.inl h0))
    · subst z; exact hp.mono (by omega)
    · exact step z (List.mem_append.mpr (Or.inr h0))

def exclusionRun (xs : List ℤ) : SuffixRun × PrefixRun :=
  let s := suffixRun xs
  (s,prefixRun 1 xs s.after)

theorem exclusionRun_exact (xs : List ℤ) :
    let q := exclusionRun xs
    q.1.whole=xs.prod ∧ q.2.excluded=omitProduct 1 xs ∧ q.1.work+q.2.work=3*xs.length := by
  dsimp only [exclusionRun]
  rw [(suffixRun_exact xs).1,(suffixRun_exact xs).2.1,(suffixRun_exact xs).2.2,
    (prefixRun_exact xs 1).1,(prefixRun_exact xs 1).2]
  exact ⟨rfl,rfl,by omega⟩

theorem exclusionRun_fits {b : ℕ} (xs : List ℤ) (h : ∀ x∈xs, Fits b x) :
    let q := exclusionRun xs
    ∀ z∈q.1.whole::(q.1.after++q.2.prefixCells++q.2.excluded), Fits (b*xs.length) z := by
  dsimp only [exclusionRun]
  rw [(suffixRun_exact xs).1,(suffixRun_exact xs).2.1]
  intro z hz
  simp only [List.mem_append,List.mem_cons] at hz
  rcases hz with rfl | ((h0|h0)|h0)
  · exact product_fits xs h
  · exact tailProducts_fits xs h z h0
  · simpa using prefixRun_fits xs 1 (Fits.one 0) h z (List.mem_append.mpr (Or.inr h0))
  · simpa using prefixRun_fits xs 1 (Fits.one 0) h z (List.mem_append.mpr (Or.inl h0))

#print axioms Fits.signedWidth
#print axioms product_fits
#print axioms sum_fits
#print axioms suffixRun_exact
#print axioms prefixRun_exact
#print axioms prefixRun_fits
#print axioms exclusionRun_exact
#print axioms exclusionRun_fits
end J9R19CompiledBits
