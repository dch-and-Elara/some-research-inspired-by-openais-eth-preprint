import V8NativeMessageC3Native

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

/-! The supplied native MAIN public layout and source address.
In particular a private point is not an arbitrary vector of theta jets:
it is a Boolean word in its true restricted measurement fibre. -/
namespace V8NativeMessage.C3.RawMain
open scoped Classical BigOperators Polynomial
open Polynomial V8PooledRange
noncomputable section

variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ]

def positiveNode {Q : ℕ} (t : Fin Q) : ℕ := t.val+1

theorem positiveNode_bounds {Q : ℕ} (t : Fin Q) : 1≤positiveNode t ∧ positiveNode t≤Q := by
  have h := t.isLt
  unfold positiveNode
  omega

/-- Public layout condition and the common coefficient denominator are
represented as data. Construction cost is not hidden in this record. -/
structure Layout (V E Γ : Type) [Fintype V] [Fintype E] [Fintype Γ] where
  R : ℕ
  Q : ℕ
  D : ℕ
  τ : ℚ
  positive_degree : 0 < R
  degree_lt_nodes : R < Q
  positive_radius : 0 < D
  group_count : 2≤Fintype.card Γ
  positive_density : 0 < τ
  density_cap : τ≤1/2
  varGroup : Fin Q → Variable V → Γ
  factorGroup : Fin Q → ClauseId V E → Γ
  variables_bound : ∀ t g,
    Fintype.card {v // varGroup t v=g} * Fintype.card Γ ≤ 2*Fintype.card (Variable V)
  rows : Fin Q → Γ → ℕ
  measure : ∀ t g, Fin (rows t g) → {v // varGroup t v=g} → ℤ
  row_norm : ∀ t g j, (∑ w : {v // varGroup t v=g}, (measure t g j w).natAbs)≤D
  row_budget : ∀ t, ((∑ g, rows t g : ℕ):ℚ)≤2*τ*Fintype.card (Variable V)
  scope : ClauseId V E → Finset (Variable V)
  replacement : ClauseId V E → Variable V → Variable V → ℚ[X]
  degree_bound : ∀ f v, v∈scope f → ∀ w, (replacement f v w).natDegree≤R
  origin : ∀ f v, v∈scope f → ∀ w, (replacement f v w).eval 0 = if w=v then 1 else 0
  annihilate : ∀ t f v, v∈scope f → ∀ g, g≠factorGroup t f →
    ∀ ξ : {w // varGroup t w=g}→ℚ,
      (∀ j : Fin (rows t g), ∑ w, (measure t g j w : ℚ)*ξ w=0) →
      ∑ w, (replacement f v w.val).eval (positiveNode t : ℚ)*ξ w=0
  scaled_integral : ∀ f v, v∈scope f → ∀ w k, ∃ a : ℤ,
    (((R-1).factorial*Q.factorial : ℕ):ℚ) * (replacement f v w).coeff k=(a:ℚ)

variable (L : Layout V E Γ)

abbrev Words (t : Fin L.Q) (g : Γ) := {v // L.varGroup t v=g} → Bool

def measured (t : Fin L.Q) (g : Γ) (x : Words L t g) (j : Fin (L.rows t g)) : ℤ :=
  ∑ w, L.measure t g j w * (if x w then 1 else 0)

def order : ℕ := 1 + (2*Fintype.card (ClauseId V E)*L.R)/L.Q

/-- The legal data (t,E,U,y,rep) used before the source chooses g. -/
structure Address where
  t : Fin L.Q
  Eset : Finset (Variable V)
  Uset : Finset (Variable V)
  correction_subset : Uset⊆Eset
  correction_order : Eset.card≤order L-1
  y : ∀ g, Fin (L.rows t g)→ℤ
  within_box : ∀ g j, -(L.D:ℤ)≤y g j ∧ y g j≤L.D
  rep : ∀ g, Words L t g
  rep_fibre : ∀ g j, measured L t g (rep g) j = y g j

abbrev Fibre (a : Address L) (g : Γ) :=
  {x : Words L a.t g // (∀ j, measured L a.t g x j=a.y g j) ∧
    ∀ w : {w // L.varGroup a.t w=g}, w.val∈a.Eset → x w=true}

def replacementWord (a : Address L) (g : Γ) (x : Fibre L a g) (w : Variable V) : Bool :=
  if h : L.varGroup a.t w=g then x.val ⟨w,h⟩
  else a.rep (L.varGroup a.t w) ⟨w,rfl⟩

theorem word_own (a : Address L) (g : Γ) (x : Fibre L a g)
    (w : {w // L.varGroup a.t w=g}) : replacementWord L a g x w.val=x.val w := by
  simp only [replacementWord,dif_pos w.property]

theorem word_other (a : Address L) (g : Γ) (x : Fibre L a g)
    (w : Variable V) (h : L.varGroup a.t w≠g) :
    replacementWord L a g x w=a.rep (L.varGroup a.t w) ⟨w,rfl⟩ := by
  simp only [replacementWord,dif_neg h]

theorem replacementWord_measures (a : Address L) (g : Γ) (x : Fibre L a g)
    (h : Γ) (j : Fin (L.rows a.t h)) :
    measured L a.t h (fun w => replacementWord L a g x w.val) j=a.y h j := by
  by_cases e : h=g
  · subst h
    have hw : (fun w : {w // L.varGroup a.t w=g} => replacementWord L a g x w.val)=x.val :=
      funext (word_own L a g x)
    rw [hw]
    exact x.property.1 j
  · have hw : (fun w : {w // L.varGroup a.t w=h} => replacementWord L a g x w.val)=a.rep h := by
      funext w
      have ew : L.varGroup a.t w.val≠g := w.property.trans_ne e
      rw [word_other L a g x w.val ew]
      cases w with
      | mk u hu =>
        simp only at hu
        cases hu
        rfl
    rw [hw]
    exact a.rep_fibre h j

def base (a : Address L) (g : Γ) (x : Fibre L a g) (f : ClauseId V E) (v : Variable V) : ℚ :=
  ∑ w, (L.replacement f v w).eval (positiveNode a.t : ℚ) *
    (if replacementWord L a g x w then 1 else 0)

/-- Exact source substitution <P(t),x^rep> +
<P(t+z)-P(t),1_U>, before taking the jet quotient. The selected point
and both arguments are independent of external switch signs. -/
def thetaPolynomial (a : Address L) (g : Γ) (x : Fibre L a g) (f : ClauseId V E)
    (v : Variable V) : ℚ[X] :=
  C (base L a g x f v) + ∑ w ∈ a.Uset,
    ((L.replacement f v w).comp (C (positiveNode a.t : ℚ)+X) -
      C ((L.replacement f v w).eval (positiveNode a.t : ℚ)))

def theta (a : Address L) (g : Γ) (x : Fibre L a g) (κ : ℕ) (f : ClauseId V E)
    (v : Variable V) : C3.Jet ℚ κ :=
  AdjoinRoot.mk ((X : ℚ[X])^κ) (thetaPolynomial L a g x f v)

theorem theta_constant (a : Address L) (g : Γ) (x : Fibre L a g) (f : ClauseId V E)
    (v : Variable V) :
    (thetaPolynomial L a g x f v).eval 0=base L a g x f v := by
  rw [thetaPolynomial,eval_add,eval_C,eval_finset_sum]
  have hz : (∑ w∈a.Uset,
      (((L.replacement f v w).comp (C (positiveNode a.t : ℚ)+X) -
        C ((L.replacement f v w).eval (positiveNode a.t : ℚ)))).eval 0)=0 := by
    refine Finset.sum_eq_zero (fun w _ => ?_)
    simp [eval_comp]
  rw [hz,add_zero]

#print axioms positiveNode_bounds
#print axioms replacementWord_measures
#print axioms word_own
#print axioms word_other
#print axioms theta_constant
end
end V8NativeMessage.C3.RawMain