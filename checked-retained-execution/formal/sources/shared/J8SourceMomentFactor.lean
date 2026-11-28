import J8SourceMoment

/-!
Column-local realization for J8. Group the literal truth-table factors
from actual matched subdivision legs by the old column on which they
depend. A selected target port only alters that row's one factor. The
same exact formulas provide source moments and all marked target masses
from local original column tables, without enumerating a joined cube.
-/

namespace J8SourceMoment

open scoped BigOperators Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {R V : Type*} {P : V → Type*}

/-- The actual old column and physical leg read by each matched binary
subdivision, at the chosen outer root node. Unmatched rows read neither. -/
structure ColumnWiring (R V : Type*) (P : V → Type*) where
  dest : R → Option V
  leg : R → Bool
  port : (r : R) → (v : V) → dest r = some v → P v

variable (w : ColumnWiring R V P) (c : ℚ)

def wireHit (r : R) : Option (Bool × (((v : V) → P v → Bool) → Bool)) :=
  match h : w.dest r with
  | none => none
  | some v => some (w.leg r, fun x => x v (w.port r v h))

theorem wireHit_none (r : R) (h : w.dest r = none) : wireHit w r = none := by
  unfold wireHit
  split
  · rfl
  · rename_i v he
    rw [h] at he
    contradiction

theorem wireHit_some (r : R) (v : V) (h : w.dest r = some v) :
    wireHit w r = some (w.leg r, fun x => x v (w.port r v h)) := by
  unfold wireHit
  split
  · rename_i he
    rw [h] at he
    contradiction
  · rename_i u he
    have hv : u = v := Option.some.inj (he.symm.trans h)
    subst u
    rfl


variable [Fintype R] [DecidableEq R] [Fintype V] [DecidableEq V]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

variable (F : (v : V) → LiteralPortCompiler.CNF (P v))

/-- The product of the distinct original nonpin column truth tables, not an
arbitrary background sum. Unary pins are the separate fields in the child. -/
def literalChild : Child R ((v : V) → P v → Bool) where
  c := c
  hit := wireHit w
  oldWeight x := ∏ v, LiteralPortCompiler.truth (F v) (x v)

theorem old_nonnegative (x : ∀ v, P v → Bool) : 0 ≤ (literalChild w c F).oldWeight x := by
  apply Finset.prod_nonneg
  intro v hv
  unfold LiteralPortCompiler.truth LiteralPortCompiler.indicator
  split_ifs <;> norm_num

theorem old_has_assignment (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F v) x = true) :
    ∃ x, 0 < (literalChild w c F).oldWeight x := by
  choose x hx using sat
  refine ⟨x, ?_⟩
  change 0 < ∏ v, (LiteralPortCompiler.truth (F v) (x v) : ℚ)
  have h (v : V) : (LiteralPortCompiler.truth (F v) (x v) : ℚ) = 1 := by
    simp [LiteralPortCompiler.truth, LiteralPortCompiler.indicator, hx v]
  simp only [h, Finset.prod_const_one, zero_lt_one]

def localRow (marked : Option (R × Bool)) (r : R) (side : Bool) (a : ℚ) : ℚ :=
  rowFactor (marker marked r) (if side = false then a else 0) (if side = true then a else 0)

/-- At most a unary contribution on each hit row: baseline, selected leg
itself, or the other leg. In particular no new inter-column interaction
is created by the first derivative. -/
theorem localRow_formula (marked : Option (R × Bool)) (r : R) (side : Bool) (a : ℚ) :
    localRow marked r side a =
    match marker marked r with
    | none => 1 - a
    | some right => if right = side then -1 else -1 + 2*a := by
  unfold localRow
  cases hm : marker marked r with
  | none =>
    cases side <;> simp [rowFactor, oldEquality_eq, TargetDerivative.equality]
  | some right =>
    cases side <;> cases right <;> simp [rowFactor, selectedEquality_eq]

def unmatchedMultiplier (marked : Option (R × Bool)) : ℚ :=
  ∏ r : {r : R // w.dest r = none}, rowFactor (marker marked r.1) (0 : ℚ) 0

def localColumnWeight (marked : Option (R × Bool)) (v : V) (z : P v → Bool) : ℚ :=
  LiteralPortCompiler.truth (F v) z *
    ∏ r : {r : R // w.dest r = some v}, localRow marked r.1 (w.leg r.1)
      (c * NativeChildRealization.bitValue ℚ (z (w.port r.1 v r.2)))

theorem weighted_column_factor (marked : Option (R × Bool)) (x : (v : V) → P v → Bool) :
    weighted (literalChild w c F) marked x =
      unmatchedMultiplier w marked * ∏ v, localColumnWeight w c F marked v (x v) := by
  classical
  let f : R → ℚ := fun r => rowFactor (marker marked r)
    (input0 (literalChild w c F) x r false) (input0 (literalChild w c F) x r true)
  have f_none (r : {r : R // w.dest r = none}) :
      f r = rowFactor (marker marked r.1) (0 : ℚ) 0 := by
    simp only [f, input0, literalChild, wireHit_none w r.1 r.2]
  have f_some (v : V) (r : {r : R // w.dest r = some v}) :
      f r = localRow marked r.1 (w.leg r.1)
        (c * NativeChildRealization.bitValue ℚ (x v (w.port r.1 v r.2))) := by
    simp only [f, input0, literalChild, wireHit_some w r.1 v r.2, localRow]
  change (∏ v, LiteralPortCompiler.truth (F v) (x v)) * (∏ r, f r) = _
  rw [← Fintype.prod_fiberwise w.dest f, Fintype.prod_option]
  simp only [f_none, f_some, unmatchedMultiplier, localColumnWeight, Finset.prod_mul_distrib]
  ring

/-- The target mass, or baseline mass with no marking, is a product of
sums over bounded original local assignments. -/
theorem marked_mass_local (marked : Option (R × Bool)) :
    (∑ x : (v : V) → P v → Bool, weighted (literalChild w c F) marked x) =
      unmatchedMultiplier w marked * ∏ v, ∑ z : P v → Bool, localColumnWeight w c F marked v z := by
  classical
  simp_rw [weighted_column_factor w c F, ← Finset.mul_sum]
  rw [← Fintype.prod_sum (localColumnWeight w c F marked)]

theorem unmatchedMultiplier_baseline : unmatchedMultiplier w none = (1 : ℚ) := by
  simp [unmatchedMultiplier, marker, rowFactor, oldEquality_eq, TargetDerivative.equality]

variable {J : Type*} [Fintype J]

/-- The actual linear tile moment also has a local evaluator. Only the
column owning a selected feature needs a nontrivial marginal; shared port
owners and repeated indices are allowed. -/
theorem source_moment_local (tile : J → Sigma P) (coef : J → ℚ)
    (nonzero : ∀ v, NativeChildRealization.mass (localColumnWeight w c F none) v ≠ 0) :
    (∑ x : (v : V) → P v → Bool, weighted (literalChild w c F) none x *
      ∑ j, coef j * NativeChildRealization.bitValue ℚ (x (tile j).1 (tile j).2)) =
        (∏ v, NativeChildRealization.mass (localColumnWeight w c F none) v) *
          ∑ j, coef j * NativeChildRealization.mean
            (localColumnWeight w c F none) (tile j).1
            (fun z => NativeChildRealization.bitValue ℚ (z (tile j).2)) := by
  simp_rw [weighted_column_factor w c F, unmatchedMultiplier_baseline w, one_mul]
  have h := NativeChildRealization.singleton_source_moment (localColumnWeight w c F none)
    (fun j : J => (tile j).1) (fun j z => NativeChildRealization.bitValue ℚ (z (tile j).2)) coef nonzero
  convert h using 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_univ]

#print axioms localRow_formula
#print axioms weighted_column_factor
#print axioms marked_mass_local
#print axioms source_moment_local

end
end J8SourceMoment
