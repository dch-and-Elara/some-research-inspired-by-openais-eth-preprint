import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
A direct formal model of the diagonal pins in the rational main-body probe
of OpenAI's interpolation algorithm.  The input row is not assumed constant:
it is built from actual coordinate swaps, their weight operator, the
power-sum polynomial and the source mismatch polynomial.  The diagonal
measurement is a product of coordinate basis rows.  The fibre sum uses
individual pin factors at their corrected argument.
-/
namespace MainProbe
open scoped BigOperators
open Polynomial
universe u v w c b

abbrev Cell (I : Type u) (S : Type v) := (I → S) × (I → S)
abbrev Vec (I : Type u) (S : Type v) := Cell I S → ℚ

variable {I : Type u} {S : Type v} [Fintype I] [DecidableEq I] [DecidableEq S]

/-- Exchange the two symbols at exactly coordinate i. -/
def swap (i : I) (u : Cell I S) : Cell I S :=
  (Function.update u.1 i (u.2 i), Function.update u.2 i (u.1 i))

omit [Fintype I] [DecidableEq S] in
theorem swap_diag (i : I) (u : Cell I S) (h : u.1 = u.2) : swap i u = u := by
  rcases u with ⟨a,d⟩
  change a = d at h
  subst d
  ext j <;> by_cases hij : j = i <;> simp [swap, hij]

omit [Fintype I] [DecidableEq S] in
theorem swap_involutive (i : I) : Function.Involutive (swap (S := S) i) := by
  intro x
  ext j <;> by_cases hij : j = i <;> simp [swap, hij]

/-- The full swap V_0, named by its action on a point. -/
def allSwap (u : Cell I S) : Cell I S := (u.2,u.1)

omit [Fintype I] [DecidableEq I] [DecidableEq S] in
theorem allSwap_diag (u : Cell I S) (h : u.1 = u.2) : allSwap u = u :=
  Prod.ext h.symm h


/-- Multiply coordinate permutation operators along a list of coordinates. -/
def swapSequence : List I → Cell I S → Cell I S
  | [], u => u
  | i::is, u => swap i (swapSequence is u)

omit [Fintype I] [DecidableEq S] in
theorem swapSequence_coordinate (l : List I) (hn : l.Nodup) (u : Cell I S) (j : I) :
    (swapSequence l u).1 j = (if j ∈ l then u.2 j else u.1 j) ∧
    (swapSequence l u).2 j = (if j ∈ l then u.1 j else u.2 j) := by
  induction l with
  | nil => simp [swapSequence]
  | cons i l ih =>
    obtain ⟨hi,hl⟩ := List.nodup_cons.mp hn
    obtain ⟨h1,h2⟩ := ih hl
    by_cases hji : j = i
    · subst j
      simp [swapSequence,swap,h1,h2,hi]
    · simp [swapSequence,swap,hji,h1,h2]

omit [Fintype I] [DecidableEq S] in
theorem allSwap_eq_sequence (l : List I) (hn : l.Nodup) (hall : ∀ i, i ∈ l) (u : Cell I S) :
    swapSequence l u = allSwap u := by
  have h (i : I) := swapSequence_coordinate l hn u i
  refine Prod.ext ?_ ?_
  · funext i
    simpa [allSwap,hall i] using (h i).1
  · funext i
    simpa [allSwap,hall i] using (h i).2


/-- W_0 = (1/2) times the sum of I - Pi_i, acting on a coefficient vector. -/
def swapWeight (x : Vec I S) (u : Cell I S) : ℚ :=
  (1/2) * ∑ i, (x u - x (swap i u))

omit [DecidableEq S] in
theorem swapWeight_diag (x : Vec I S) (u : Cell I S) (h : u.1 = u.2) :
    swapWeight x u = 0 := by
  simp [swapWeight, swap_diag _ _ h]

def iterWeight : ℕ → Vec I S → Vec I S
  | 0, x => x
  | k+1, x => swapWeight (iterWeight k x)

/-- The polynomial used in the printed scheme, independently of the tail interval proof. -/
noncomputable def intervalPolynomial (start width : ℕ) : ℚ[X] :=
  C ((-1 : ℚ)^start) * ∑ j ∈ Finset.range width,
    C (((-2 : ℚ)^j) / (Nat.factorial j : ℚ)) *
      ∏ a ∈ Finset.range j, (X - C (↑(start+a) : ℚ))

/-- V_0 p(W_0), applied to x. The general p includes the source p_I. -/
def mix (p : ℚ[X]) (x : Vec I S) (u : Cell I S) : ℚ :=
  ∑ j ∈ Finset.range (p.natDegree+1), p.coeff j * iterWeight j x (allSwap u)

omit [DecidableEq S] in
theorem mix_diag (p : ℚ[X]) (x : Vec I S) (u : Cell I S) (h : u.1 = u.2) :
    mix p x u = p.coeff 0 * x u := by
  classical
  have h0 : 0 ∈ Finset.range (p.natDegree+1) := Finset.mem_range.mpr (Nat.zero_lt_succ _)
  rw [mix, Finset.sum_eq_single_of_mem 0 h0]
  · simp [iterWeight, allSwap_diag _ h]
  · intro j _ hj
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    change p.coeff (k+1) * swapWeight (iterWeight k x) (allSwap u) = 0
    have hswap : swapWeight (iterWeight k x) (allSwap u) = 0 :=
      swapWeight_diag (iterWeight k x) (allSwap u) h.symm
    rw [hswap,mul_zero]

/-- Standard coordinate vector, choosing instances locally for finite function domains. -/
noncomputable def delta (u : Cell I S) (x : Cell I S) : ℚ := by
  classical
  exact if x = u then 1 else 0

/-- Entry [u,y] of V_0 p(W_0), evaluated against the y-th coordinate basis vector. -/
noncomputable def mixingEntry (p : ℚ[X]) (u y : Cell I S) : ℚ :=
  mix p (delta y) u

/-- E_{u,y} consists exactly of wrong-symbol coordinates, and the printed
polynomial puts a factor 1-T/t at each of them.  The map node supplies t. -/
noncomputable def mismatch (node : I → ℚ) (u y : Cell I S) : ℚ[X] :=
  ∏ i ∈ (Finset.univ.filter fun i => y.1 i ≠ u.2 i), (1-X*C ((node i)⁻¹))

omit [DecidableEq I] in
theorem mismatch_diag (node : I → ℚ) (u : Cell I S) (h : u.1 = u.2) :
    mismatch node u u = 1 := by
  simp [mismatch,h]

/-- Coefficient of the source formula delta_u(I-M_0) + M_0[u,y] phi[u,y] delta_y.
Adding terms with zero coefficient changes nothing. -/
noncomputable def sourceRow (p : ℚ[X]) (node : I → ℚ) (u y : Cell I S) : ℚ[X] :=
  C (delta y u - mixingEntry p u y) + C (mixingEntry p u y) * mismatch node u y

/-- The genuinely computed row is the unchanged coordinate, at every T. -/
theorem sourceRow_diag (p : ℚ[X]) (node : I → ℚ) (u : Cell I S) (h : u.1 = u.2) :
    ∀ y, sourceRow p node u y = C (delta y u) := by
  classical
  intro y
  by_cases hy : u = y
  · subst y
    rw [sourceRow,mismatch_diag _ _ h,mul_one, ← C_add]
    congr 1
    ring
  · have hz : delta y u = 0 := by simp [delta,hy]
    have hm : mixingEntry p u y = 0 := by
      unfold mixingEntry
      rw [mix_diag p (delta y) u h,hz,mul_zero]
    simp [sourceRow,hm,hz]

variable [Fintype S]

/-- The tensor product of e_(a(i),a(i)) over coordinates. -/
def weightZeroRow (u y : Cell I S) : ℚ :=
  ∏ i, if y.1 i = u.1 i ∧ y.2 i = u.1 i then 1 else 0

omit [DecidableEq I] [Fintype S] in
theorem weightZeroRow_delta (u : Cell I S) (h : u.1 = u.2) :
    weightZeroRow u = delta u := by
  classical
  funext y
  by_cases hy : y = u
  · subst y
    simp [weightZeroRow,delta,h]
  · have hd : ∃ i, ¬(y.1 i = u.1 i ∧ y.2 i = u.1 i) := by
      by_contra! hall
      apply hy
      exact Prod.ext (funext fun i => (hall i).1)
        (funext fun i => (hall i).2.trans (congrFun h i))
    obtain ⟨i,hi⟩ := hd
    have hp : weightZeroRow u y = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    simp [hp,delta,hy]

omit [Fintype S] in
theorem weightZeroRow_weight (u : Cell I S) (h : u.1 = u.2) :
    swapWeight (weightZeroRow u) = 0 := by
  classical
  rw [weightZeroRow_delta _ h]
  funext x
  have hh : ∀ i, swap i x = u ↔ x = u := by
    intro i
    constructor
    · intro he
      calc
        x = swap i (swap i x) := (swap_involutive i x).symm
        _ = u := by rw [he,swap_diag _ _ h]
    · intro he
      rw [he,swap_diag _ _ h]
  simp [swapWeight,delta,hh]

#print axioms allSwap_eq_sequence
#print axioms sourceRow_diag
#print axioms weightZeroRow_delta
#print axioms weightZeroRow_weight


/-- All tracked pins are diagonal and lie at designated occupied copy slots.
The other source factors and slots are not required to be diagonal. -/
structure DiagonalLayout (I : Type u) (S : Type v) (X : Type w)
    (Copy : Type c) (Pin : Type b) where
  occupied : Copy → Cell I S → Option X
  variableWord : X → I → S
  slot : Pin → Cell I S
  copy : Pin → Copy
  pinVar : Pin → X
  localSlot : ∀ p, occupied (copy p) (slot p) = some (pinVar p)
  variableLabel : ∀ p, variableWord (pinVar p) = (slot p).1
  diagonal : ∀ p, (slot p).1 = (slot p).2

variable {X : Type w} {Copy : Type c} {Pin : Type b}


def boolRat : Bool → ℚ
  | false => 0
  | true => 1

theorem boolRat_injective : Function.Injective boolRat := by
  intro x y h
  cases x <;> cases y <;> simp_all [boolRat]

/-- The source copy embedding. Vacant positions are filled by zero. -/
def embedded (D : DiagonalLayout I S X Copy Pin) (c : Copy) (x : X → ℚ) :
    Vec I S := fun u => (D.occupied c u).elim 0 x

omit [Fintype I] [DecidableEq I] [DecidableEq S] [Fintype S] in
theorem embedded_pin (D : DiagonalLayout I S X Copy Pin) (p : Pin) (x : X → ℚ) :
    embedded D (D.copy p) x (D.slot p) = x (D.pinVar p) := by
  simp [embedded,D.localSlot]

/-- Restrict the copied exceptional e_(a,a) row to the actual variables of group g.
The zero row when zero belongs to the interval records that this one row then
is absent. No conditions on other exceptional rows are encoded here. -/
noncomputable def groupMeasurement (D : DiagonalLayout I S X Copy Pin)
    (interval : Finset ℕ) (t : I) (g : S) (p : Pin) (x : X → Bool) : ℚ :=
  if 0 ∈ interval then 0 else
    ∑ u, weightZeroRow (D.slot p) u * embedded D (D.copy p)
      (fun j => if D.variableWord j t = g then boolRat (x j) else 0) u

theorem groupMeasurement_pin (D : DiagonalLayout I S X Copy Pin)
    (interval : Finset ℕ) (hOutside : 0 ∉ interval) (t : I) (g : S) (p : Pin)
    (owned : (D.slot p).2 t = g) (x : X → Bool) :
    groupMeasurement D interval t g p x = boolRat (x (D.pinVar p)) := by
  classical
  unfold groupMeasurement
  rw [if_neg hOutside, weightZeroRow_delta _ (D.diagonal p)]
  rw [Finset.sum_eq_single (D.slot p)]
  · have hm : D.variableWord (D.pinVar p) t = g :=
      (congrFun (D.variableLabel p) t).trans ((congrFun (D.diagonal p) t).trans owned)
    simp only [delta]
    rw [embedded_pin]
    simp [hm]
  · intro u _ hu
    simp [delta,hu]
  · simp

/-- The actual excerpted expression P(t)·x + (P(t+z)-P(t))·1_U. -/
noncomputable def correctedArgument (r : Cell I S → ℚ[X]) (t : ℚ)
    (x correction : Vec I S) : ℚ[X] :=
  (∑ u, C ((r u).eval t) * C (x u)) +
    (∑ u, ((r u).comp (Polynomial.X + C t) - C ((r u).eval t)) * C (correction u))

theorem correctedArgument_constant (p : Cell I S) (t : ℚ) (x correction : Vec I S) :
    correctedArgument (fun u => C (delta u p)) t x correction = C (x p) := by
  classical
  simp only [correctedArgument,eval_C,C_comp,sub_self,zero_mul,Finset.sum_const_zero,add_zero]
  rw [Finset.sum_eq_single p]
  · simp [delta]
  · intro u _ hu
    simp [delta,Ne.symm hu]
  · simp

theorem correctedArgument_pin (D : DiagonalLayout I S X Copy Pin)
    (f : ℚ[X]) (node : I → ℚ) (t : I) (p : Pin) (x U : X → Bool) :
    correctedArgument (sourceRow f node (D.slot p)) (node t)
      (embedded D (D.copy p) (fun j => boolRat (x j)))
      (embedded D (D.copy p) (fun j => boolRat (U j))) =
      C (boolRat (x (D.pinVar p))) := by
  have he : sourceRow f node (D.slot p) = fun u => C (delta u (D.slot p)) :=
    funext (sourceRow_diag f node _ (D.diagonal p))
  rw [he, correctedArgument_constant, embedded_pin]

/-- The actual unary pin factor with a Boolean sign. -/
noncomputable def pinFactor (sign : Bool) (arg : ℚ[X]) : ℚ[X] :=
  if sign then arg else 1 - arg

theorem pinFactor_on_bit (s b : Bool) :
    pinFactor s (C (boolRat b)) = if s = b then 1 else 0 := by
  cases s <;> cases b <;> simp [pinFactor,boolRat]

/-- The diagonal pins selected by this source coordinate and group. -/
def ownedPins [DecidableEq Pin] (D : DiagonalLayout I S X Copy Pin)
    (t : I) (g : S) (tracked : Finset Pin) : Finset Pin :=
  tracked.filter fun p => (D.slot p).2 t = g

/-- The other restrictions and factors are kept as base and other.  The address
supplies in particular a value w for each copied weight-zero measurement; raw
fibre sums factor at their own corrected arguments. Other factors may depend
arbitrarily on the private point and, for the zero claim, even on the signs. -/
noncomputable def sourceGroupProbe [DecidableEq Pin] (D : DiagonalLayout I S X Copy Pin)
    (interval : Finset ℕ) (f : ℚ[X]) (node : I → ℚ) (t : I) (g : S)
    (tracked : Finset Pin) (base : Finset (X → Bool)) (U : X → Bool)
    (w sigma : Pin → Bool) (other : (X → Bool) → ℚ[X]) : ℚ[X] := by
  classical
  exact ∑ x ∈ base.filter (fun x => ∀ p ∈ ownedPins D t g tracked,
      groupMeasurement D interval t g p x = boolRat (w p)),
    other x * ∏ p ∈ ownedPins D t g tracked,
      pinFactor (sigma p) (correctedArgument (sourceRow f node (D.slot p)) (node t)
        (embedded D (D.copy p) (fun j => boolRat (x j)))
        (embedded D (D.copy p) (fun j => boolRat (U j))))

/-- A wrong sign in a tracked pin makes EVERY coefficient of the group jet zero.
An arbitrary polynomial truncation can subsequently be applied to this identity. -/
theorem sourceGroupProbe_off [DecidableEq Pin] (D : DiagonalLayout I S X Copy Pin)
    (interval : Finset ℕ) (hOutside : 0 ∉ interval)
    (f : ℚ[X]) (node : I → ℚ) (t : I) (g : S)
    (tracked : Finset Pin) (base : Finset (X → Bool)) (U : X → Bool)
    (w sigma : Pin → Bool) (other : (X → Bool) → ℚ[X])
    (p : Pin) (hpin : p ∈ ownedPins D t g tracked) (hwrong : sigma p ≠ w p) :
    sourceGroupProbe D interval f node t g tracked base U w sigma other = 0 := by
  classical
  unfold sourceGroupProbe
  apply Finset.sum_eq_zero
  intro x hx
  have hmeas := (Finset.mem_filter.mp hx).2 p hpin
  have hown := (Finset.mem_filter.mp hpin).2
  rw [groupMeasurement_pin D interval hOutside t g p hown] at hmeas
  have hbit := boolRat_injective hmeas
  refine mul_eq_zero.mpr (Or.inr (Finset.prod_eq_zero hpin ?_))
  rw [correctedArgument_pin, hbit, pinFactor_on_bit, if_neg hwrong]

/-- Coefficient-wise version, covering all choices of truncation order. -/
theorem sourceGroupProbe_coeff_off [DecidableEq Pin] (D : DiagonalLayout I S X Copy Pin)
    (interval : Finset ℕ) (hOutside : 0 ∉ interval)
    (f : ℚ[X]) (node : I → ℚ) (t : I) (g : S)
    (tracked : Finset Pin) (base : Finset (X → Bool)) (U : X → Bool)
    (w sigma : Pin → Bool) (other : (X → Bool) → ℚ[X])
    (p : Pin) (hpin : p ∈ ownedPins D t g tracked) (hwrong : sigma p ≠ w p) (j : ℕ) :
    (sourceGroupProbe D interval f node t g tracked base U w sigma other).coeff j = 0 := by
  rw [sourceGroupProbe_off D interval hOutside f node t g tracked base U w sigma other p hpin hwrong]
  simp

#print axioms groupMeasurement_pin
#print axioms correctedArgument_pin
#print axioms pinFactor_on_bit
#print axioms sourceGroupProbe_off
#print axioms sourceGroupProbe_coeff_off


/-- Completed root probe at one fixed (t,E,U,y), before truncating at any order. -/
noncomputable def sourceCompletedProbe [DecidableEq Pin] (D : DiagonalLayout I S X Copy Pin)
    (interval : Finset ℕ) (f : ℚ[X]) (node : I → ℚ) (t : I) (tracked : Finset Pin)
    (base : S → Finset (X → Bool)) (U : X → Bool) (w sigma : Pin → Bool)
    (other : S → (X → Bool) → ℚ[X]) : ℚ[X] :=
  ∏ g, sourceGroupProbe D interval f node t g tracked (base g) U w sigma (other g)

theorem sourceCompletedProbe_off [DecidableEq Pin] (D : DiagonalLayout I S X Copy Pin)
    (interval : Finset ℕ) (hOutside : 0 ∉ interval)
    (f : ℚ[X]) (node : I → ℚ) (t : I) (tracked : Finset Pin)
    (base : S → Finset (X → Bool)) (U : X → Bool) (w sigma : Pin → Bool)
    (other : S → (X → Bool) → ℚ[X]) (p : Pin) (hpin : p ∈ tracked) (hwrong : sigma p ≠ w p) :
    sourceCompletedProbe D interval f node t tracked base U w sigma other = 0 := by
  classical
  let g := (D.slot p).2 t
  have hp : p ∈ ownedPins D t g tracked := Finset.mem_filter.mpr ⟨hpin,rfl⟩
  exact Finset.prod_eq_zero (Finset.mem_univ g)
    (sourceGroupProbe_off D interval hOutside f node t g tracked (base g) U w sigma (other g)
      p hp hwrong)

/-- A fibre address fixes exactly the signs in a finite set. -/
noncomputable def pinCylinder [Fintype Pin] (fixed : Finset Pin) (w : Pin → Bool) :
    Finset (Pin → Bool) := by
  classical
  exact Finset.univ.filter (fun s => ∀ p ∈ fixed, s p = w p)

theorem mem_pinCylinder [Fintype Pin] (fixed : Finset Pin) (w s : Pin → Bool) :
    s ∈ pinCylinder fixed w ↔ ∀ p ∈ fixed, s p = w p := by
  classical
  simp [pinCylinder]

noncomputable def cylinderFreeEquiv (fixed : Finset Pin) (w : Pin → Bool) :
    {s : Pin → Bool // ∀ p ∈ fixed, s p = w p} ≃ ({p // p ∉ fixed} → Bool) := by
  classical
  refine {
    toFun := fun s p => s.1 p.1
    invFun := fun z => ⟨fun p => if hp : p ∈ fixed then w p else z ⟨p,hp⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro p hp
    simp [hp]
  · intro s
    apply Subtype.ext
    funext p
    by_cases h : p ∈ fixed
    · simp [h,(s.2 p h)]
    · simp [h]
  · intro z
    funext p
    simp [p.2]

theorem pinCylinder_card [Fintype Pin] (fixed : Finset Pin) (w : Pin → Bool) :
    (pinCylinder fixed w).card = 2 ^ (Fintype.card Pin - fixed.card) := by
  classical
  let e := (Equiv.subtypeEquivRight fun s => mem_pinCylinder fixed w s).trans
    (cylinderFreeEquiv fixed w)
  have hs := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
      Fintype.card_coe] at hs
  exact hs

theorem sourceGroupProbe_outside_cylinder [Fintype Pin] [DecidableEq Pin]
    (D : DiagonalLayout I S X Copy Pin) (interval : Finset ℕ) (hOutside : 0 ∉ interval)
    (f : ℚ[X]) (node : I → ℚ) (t : I) (g : S)
    (tracked : Finset Pin) (base : Finset (X → Bool)) (U : X → Bool)
    (w sigma : Pin → Bool) (other : (X → Bool) → ℚ[X])
    (off : sigma ∉ pinCylinder (ownedPins D t g tracked) w) :
    sourceGroupProbe D interval f node t g tracked base U w sigma other = 0 := by
  classical
  rw [mem_pinCylinder] at off
  push_neg at off
  obtain ⟨p,hp,hw⟩ := off
  exact sourceGroupProbe_off D interval hOutside f node t g tracked base U w sigma other p hp hw

theorem sourceCompletedProbe_outside_cylinder [Fintype Pin] [DecidableEq Pin]
    (D : DiagonalLayout I S X Copy Pin) (interval : Finset ℕ) (hOutside : 0 ∉ interval)
    (f : ℚ[X]) (node : I → ℚ) (t : I) (tracked : Finset Pin)
    (base : S → Finset (X → Bool)) (U : X → Bool) (w sigma : Pin → Bool)
    (other : S → (X → Bool) → ℚ[X]) (off : sigma ∉ pinCylinder tracked w) :
    sourceCompletedProbe D interval f node t tracked base U w sigma other = 0 := by
  classical
  rw [mem_pinCylinder] at off
  push_neg at off
  obtain ⟨p,hp,hw⟩ := off
  exact sourceCompletedProbe_off D interval hOutside f node t tracked base U w sigma other p hp hw

#print axioms sourceCompletedProbe_off
#print axioms pinCylinder_card
#print axioms sourceGroupProbe_outside_cylinder
#print axioms sourceCompletedProbe_outside_cylinder


/-- A_0 in the printed formula, before taking its natural representative. -/
def printedStart (r Q R : ℕ) : ℤ :=
  ⌊(Q : ℚ)*((r : ℚ)-1)/(2*(r : ℚ)) - ((R : ℚ)-1)/2⌋

/-- The published interval consists of R consecutive weights starting at A_0. -/
def printedInterval (r Q R : ℕ) : Finset ℕ :=
  (Finset.range R).image (fun j => (printedStart r Q R).toNat + j)

theorem printedStart_pos {r Q R : ℕ} (hr : 2 ≤ r) (hR : 32 ≤ R) (hQ : 6*R ≤ Q) :
    0 < printedStart r Q R := by
  unfold printedStart
  apply Int.floor_pos.mpr
  have hr' : (2 : ℚ) ≤ r := by exact_mod_cast hr
  have hR' : (32 : ℚ) ≤ R := by exact_mod_cast hR
  have hQ' : (6 : ℚ)*(R : ℚ) ≤ Q := by exact_mod_cast hQ
  have hμ : (Q : ℚ)/4 ≤ (Q : ℚ)*((r : ℚ)-1)/(2*(r : ℚ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(r : ℚ))).mpr
    have hh : 0 ≤ (Q : ℚ)*((r : ℚ)-2) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  linarith

/-- Consequently the actual published interval retains the zero-weight row at
every size where the paper's explicit parameter guards pass. -/
theorem zero_not_mem_printedInterval {r Q R : ℕ} (hr : 2 ≤ r) (hR : 32 ≤ R) (hQ : 6*R ≤ Q) :
    0 ∉ printedInterval r Q R := by
  intro hz
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hz
  have hp := printedStart_pos hr hR hQ
  have hnat : 0 < (printedStart r Q R).toNat := by omega
  omega

#print axioms zero_not_mem_printedInterval

end MainProbe
