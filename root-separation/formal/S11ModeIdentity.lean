
import S11Schedule

noncomputable section
namespace S11

open scoped BigOperators

variable {G R : Type*} [Fintype G] [CommSemiring R]

/-- At a fixed node and probe, rows and bits are partitioned by group.
    A mode lives at its target. Its tile read uses only source bits.
    The normalized row coefficients have their powers of two factored out. -/
structure AffinePacket (G R : Type*) where
  Bits : G → Type
  Rows : G → Type
  TargetMode : G → Type
  source : (Σ g, TargetMode g) → G
  weight : (Σ g, TargetMode g) → ℕ
  old : (g : G) → Bits g → R
  normalized : (g : G) → Bits g → Rows g → Option (TargetMode g) → R
  readTile : (z : Σ g, TargetMode g) → Bits (source z) → R

namespace AffinePacket

open Classical

variable (A : AffinePacket G R)
variable [∀ g, Fintype (A.Bits g)] [∀ g, Fintype (A.Rows g)]
variable [∀ g, Fintype (A.TargetMode g)]

abbrev Z := Σ g, A.TargetMode g
abbrev LocalChoice (g : G) := A.Rows g → Option (A.TargetMode g)
abbrev Local (g : G) := A.Bits g × A.LocalChoice g

def weightOption (g : G) : Option (A.TargetMode g) → ℕ :=
  Option.elim' 0 (fun z => A.weight ⟨g,z⟩)

def row (g : G) (x : A.Bits g) (r : A.Rows g) (o : Option (A.TargetMode g)) : R :=
  (2 : R) ^ A.weightOption g o * A.normalized g x r o

def uses {g : G} (c : A.LocalChoice g) (z : A.TargetMode g) : ℕ :=
  Fintype.card {r // c r = some z}

def exponents (x : ∀ g, A.Local g) (z : A.Z) : ℕ := A.uses (x z.1).2 z.2

def budget (β : A.Z → ℕ) : ℕ := ∑ z, A.weight z * β z

def oldAndRows (g : G) (x : A.Local g) : R :=
  A.old g x.1 * ∏ r, A.row g x.1 r (x.2 r)

def tileProduct (β : A.Z → ℕ) (g : G) (x : A.Bits g) : R :=
  ∏ z : {z : A.Z // A.source z = g}, A.readTile z.val (z.property.symm ▸ x) ^ β z.val

def accepts (β : A.Z → ℕ) (g : G) (x : A.Local g) : Prop :=
  ∀ z, A.uses x.2 z = β ⟨g,z⟩

/-- Actual coefficient extraction by enumerating one term per affine row.
    Every accepted choice contributes its coefficient and its source tile powers. -/
def child (β : A.Z → ℕ) (g : G) : R := by
  classical
  exact ∑ x : A.Local g, if A.accepts β g x
    then A.oldAndRows g x * A.tileProduct β g x.1 else 0

def sample : R := by
  classical
  exact ∑ X : ∀ g, A.Bits g,
    ∏ g, A.old g (X g) * ∏ r, ∑ o : Option (A.TargetMode g),
      A.row g (X g) r o * o.elim' 1 (fun z => A.readTile ⟨g,z⟩ (X (A.source ⟨g,z⟩)))

def expandedTerm (x : ∀ g, A.Local g) : R :=
  ∏ g, A.oldAndRows g (x g) * A.tileProduct (A.exponents x) g (x g).1

private theorem prod_options {U T H : Type*} [Fintype U] [Fintype T] [CommMonoid H]
    (c : U → Option T) (f : T → H) :
    ∏ u, (c u).elim' 1 f =
      ∏ t, f t ^ Fintype.card {u // c u = some t} := by
  classical
  rw [← Fintype.prod_fiberwise' c (fun o => o.elim' 1 f), Fintype.prod_option]
  simp

private theorem global_tile (β : A.Z → ℕ) (x : ∀ g, A.Local g) :
    (∏ g, A.tileProduct β g (x g).1) =
      ∏ z : A.Z, A.readTile z ((x (A.source z)).1) ^ β z := by
  classical
  rw [← Fintype.prod_fiberwise A.source]
  apply Finset.prod_congr rfl
  intro g _
  unfold tileProduct
  apply Finset.prod_congr rfl
  rintro ⟨z,h⟩ _
  subst g
  rfl

private def localEquiv :
    ((∀ g, A.Bits g) × (∀ g, A.LocalChoice g)) ≃ (∀ g, A.Local g) where
  toFun x g := (x.1 g, x.2 g)
  invFun x := (fun g => (x g).1, fun g => (x g).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sample_expand : A.sample = ∑ x : ∀ g, A.Local g, A.expandedTerm x := by
  classical
  unfold sample
  simp_rw [Fintype.prod_sum, Finset.mul_sum]
  simp_rw [Fintype.prod_sum]
  let F (z : (∀ g, A.Bits g) × (∀ g, A.LocalChoice g)) : R :=
    ∏ g, A.old g (z.1 g) * ∏ r, A.row g (z.1 g) r (z.2 g r) *
      (z.2 g r).elim' 1 (fun m => A.readTile ⟨g,m⟩ (z.1 (A.source ⟨g,m⟩)))
  change (∑ X, ∑ C, F (X,C)) = _
  rw [← Fintype.sum_prod_type F]
  apply Fintype.sum_equiv A.localEquiv
  rintro ⟨X, choices⟩
  simp only [expandedTerm, Finset.prod_mul_distrib, global_tile, oldAndRows]
  simp only [exponents, localEquiv, Equiv.coe_fn_mk]
  rw [Fintype.prod_sigma]
  simp only [F, Finset.prod_mul_distrib, ← mul_assoc]
  congr 1
  apply Finset.prod_congr rfl
  intro g _
  rw [prod_options (choices g)]
  rfl

private theorem exponents_weight (x : ∀ g, A.Local g) :
    (∑ g, ∑ r, A.weightOption g ((x g).2 r)) = A.budget (A.exponents x) := by
  classical
  rw [budget, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Fintype.sum_fiberwise' (x g).2 (A.weightOption g), Fintype.sum_option]
  simp [weightOption, exponents, uses, mul_comm]

/-- Overweight terms vanish before regrouping. This uses the actual
    coefficient factors from the printed expansion, with no zero-test on
    a full sample or an assumption about the recursion identity. -/
theorem expanded_zero (p : ℕ) (hp : (2 : R)^p = 0) (x : ∀ g, A.Local g)
    (h : p ≤ A.budget (A.exponents x)) : A.expandedTerm x = 0 := by
  classical
  let β := A.exponents x
  have hw : (2 : R) ^ A.budget β = 0 := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk, pow_add, hp, zero_mul]
  have he : A.expandedTerm x =
      (∏ g, A.old g (x g).1) *
      ((2 : R) ^ A.budget β *
        (∏ g, ∏ r, A.normalized g (x g).1 r ((x g).2 r))) *
      ∏ g, A.tileProduct β g (x g).1 := by
    simp only [expandedTerm, oldAndRows, row, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, exponents_weight, β]
  rw [he, hw, zero_mul, mul_zero, zero_mul]

def feasible (p : ℕ) : Finset (A.Z → Fin p) := by
  classical
  exact Finset.univ.filter fun β => A.budget (fun z => (β z).val) < p

theorem exponent_lt_budget (z : A.Z) (β : A.Z → ℕ) (hw : 0 < A.weight z) :
    β z ≤ A.budget β := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun z => A.weight z * β z)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)
  exact (Nat.le_mul_of_pos_left _ hw).trans h

private theorem product_child (β : A.Z → ℕ) :
    (∏ g, A.child β g) = ∑ x : ∀ g, A.Local g,
      if A.exponents x = β then A.expandedTerm x else 0 := by
  classical
  unfold child
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : A.exponents x = β
  · have h (g) : A.accepts β g (x g) := fun z => congrFun hx ⟨g,z⟩
    simp only [h, hx, if_true, expandedTerm]
  · have h : ∃ g, ¬ A.accepts β g (x g) := by
      by_contra! hn
      exact hx (funext fun z => hn z.1 z.2)
    obtain ⟨g,hg⟩ := h
    rw [if_neg hx]
    apply Finset.prod_eq_zero (Finset.mem_univ g)
    rw [if_neg hg]

theorem recursion_identity (p : ℕ) (hp : (2 : R)^p = 0) (hw : ∀ z, 0 < A.weight z) :
    A.sample = ∑ β ∈ A.feasible p, ∏ g, A.child (fun z => (β z).val) g := by
  classical
  rw [A.sample_expand]
  simp_rw [A.product_child]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : A.budget (A.exponents x) < p
  · let β : A.Z → Fin p := fun z => ⟨A.exponents x z,
      (A.exponent_lt_budget z _ (hw z)).trans_lt h⟩
    have hb : β ∈ A.feasible p := by simpa [feasible, β] using h
    rw [Finset.sum_eq_single_of_mem β hb]
    · rw [if_pos rfl]
    · intro c _ hne
      apply if_neg
      intro he
      apply hne
      funext z
      exact Fin.ext (congrFun he z).symm
  · rw [A.expanded_zero p hp x (Nat.le_of_not_gt h)]
    simp

#print axioms sample_expand
#print axioms expanded_zero
#print axioms recursion_identity

end AffinePacket
end S11

