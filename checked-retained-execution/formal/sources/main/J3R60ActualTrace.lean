import J3R60Border
import J3R60DetWidth
import J3R60Clearing

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000

/-! Every actual forward invocation of R59's recursive matrix transformation
has integer active cells, bounded cross numerators and exact nonzero
division. The recursion follows the first pivot found by the same scan. -/
namespace J3R60
open Matrix J3R59
open scoped BigOperators

universe u

def IntSized (T : ℕ) (x : ℚ) : Prop :=
  ∃ z : ℤ, x = (z : ℚ) ∧ z.natAbs ≤ T

def ExactIntegerDivision (T : ℕ) (num den ans : ℚ) : Prop :=
  ∃ a d x : ℤ, num = (a : ℚ) ∧ den = (d : ℚ) ∧ ans = (x : ℚ) ∧
    a.natAbs ≤ T ∧ d ≠ 0 ∧ a = d * x

theorem lifted_det {K I J : Type*} [Fintype K] [DecidableEq K]
    (X : I → J → ℤ) (pr : K → I) (pc : K → J) :
    (window (fun i j => (X i j : ℚ)) pr pc).det = ((window X pr pc).det : ℚ) :=
  ((Int.castRingHom ℚ).map_det (window X pr pc)).symm

theorem core_sized {K I J : Type*} [Fintype K] [DecidableEq K]
    (X : I → J → ℤ) (pr : K → I) (pc : K → J) (T N : ℕ)
    (hT : 1 ≤ T) (hX : ∀ i j, (X i j).natAbs ≤ T) (hK : Fintype.card K ≤ N) :
    IntSized (minorCap T N) (window (fun i j => (X i j : ℚ)) pr pc).det := by
  refine ⟨(window X pr pc).det,lifted_det X pr pc,?_⟩
  exact (determinant_leibniz_height (window X pr pc) T
    (fun i j => hX (pr i) (pc j))).trans (minorCap_mono_degree hT hK)

theorem single_border_sized {K I J : Type*} [Fintype K] [DecidableEq K]
    (X : I → J → ℤ) (pr : K → I) (pc : K → J) (r : I) (c : J)
    (T N : ℕ) (hT : 1 ≤ T) (hX : ∀ i j, (X i j).natAbs ≤ T)
    (hK : Fintype.card K + 1 ≤ N) :
    IntSized (minorCap T N) (bordered (fun i j => (X i j : ℚ)) pr pc r c) :=
  core_sized X (push pr r) (push pc c) T N hT hX (by simpa using hK)

theorem exact_cross_from_integer_cells {T : ℕ} {a b c e d : ℚ}
    (ha : IntSized T a) (hb : IntSized T b) (hc : IntSized T c) (he : IntSized T e)
    (hd : IntSized T d) (hne : d ≠ 0) (hq : IntSized T ((a*b-c*e)/d)) :
    ExactIntegerDivision (2*T^2) (a*b-c*e) d ((a*b-c*e)/d) := by
  obtain ⟨ai,hei,hai⟩ := ha
  obtain ⟨bi,heb,hbi⟩ := hb
  obtain ⟨ci,hec,hci⟩ := hc
  obtain ⟨ei,hee,hei'⟩ := he
  obtain ⟨di,hed,_⟩ := hd
  obtain ⟨qi,heq,_⟩ := hq
  have hn : a*b-c*e = ((ai*bi-ci*ei : ℤ) : ℚ) := by
    rw [hei,heb,hec,hee]
    push_cast
    rfl
  refine ⟨ai*bi-ci*ei,di,qi,hn,hed,heq,cross_numerator_height _ _ _ _ _ hai hbi hci hei',?_,?_⟩
  · intro hz
    exact hne (by rw [hed,hz]; rfl)
  · have eqQ := (div_eq_iff hne).mp heq
    rw [hn,hed] at eqQ
    exact mul_comm di qi ▸ (by exact_mod_cast eqQ : ai * bi - ci * ei = qi * di)

def StateBound {I : Type*} {n : ℕ} (T : ℕ) (A : I → Fin n → ℚ) (b : I → ℚ) (prev : ℚ) : Prop :=
  (∀ r j, IntSized T (A r j)) ∧ (∀ r, IntSized T (b r)) ∧ IntSized T prev

def StepBound {I : Type*} {n : ℕ} (T : ℕ) (A : I → Fin (n+1) → ℚ)
    (b : I → ℚ) (p : I) (prev : ℚ) : Prop :=
  (∀ r j, ExactIntegerDivision (2*T^2)
      (A p 0 * A r j.succ - A r 0 * A p j.succ) prev (tailMatrix A p prev r j)) ∧
    (∀ r, ExactIntegerDivision (2*T^2)
      (A p 0 * b r - A r 0 * b p) prev (tailRhs A b p prev r))

/-- A proposition about the same ordered pivot trace as `fractionFree`.
An unsuccessful scan has no subsequent arithmetic updates. -/
def ForwardBound {I : Type*} (rows : List I) (T : ℕ) :
    (n : ℕ) → (I → Fin n → ℚ) → (I → ℚ) → ℚ → Prop
  | 0, A, b, prev => StateBound T A b prev
  | n+1, A, b, prev => StateBound T A b prev ∧
    match rows.find? (fun r => decide (A r 0 ≠ 0)) with
    | none => True
    | some p => StepBound T A b p prev ∧
      ForwardBound rows T n (tailMatrix A p prev) (tailRhs A b p prev) (A p 0)

/-- Follow every actual pivot, extending the witnessed original ordered
minor. No external pivot schedule or per-round height bounds are inputs. -/
theorem forward_bordered {I J : Type*} (rows : List I) (T N : ℕ)
    (X : I → J → ℤ) (hT : 1 ≤ T) (hX : ∀ i j, (X i j).natAbs ≤ T)
    (n : ℕ) {K : Type u} [Fintype K] [DecidableEq K]
    (pr : K → I) (pc : K → J) (col : Fin n → J) (rhs : J)
    (hsize : Fintype.card K + n + 1 ≤ N)
    (hprev : (window (fun i j => (X i j : ℚ)) pr pc).det ≠ 0) :
    ForwardBound rows (minorCap T N) n
      (fun r j => bordered (fun i l => (X i l : ℚ)) pr pc r (col j))
      (fun r => bordered (fun i l => (X i l : ℚ)) pr pc r rhs)
      (window (fun i j => (X i j : ℚ)) pr pc).det := by
  let X' := fun i j => (X i j : ℚ)
  let V := minorCap T N
  let prev := (window X' pr pc).det
  let b := fun r => bordered X' pr pc r rhs
  have hw (r c) : IntSized V (bordered X' pr pc r c) :=
    single_border_sized X pr pc r c T N hT hX (by omega)
  have hd : IntSized V prev := core_sized X pr pc T N hT hX (by omega)
  cases n with
  | zero =>
    rw [ForwardBound]
    exact ⟨fun _ j => j.elim0,fun r => hw r rhs,hd⟩
  | succ n =>
    let A : I → Fin (n+1) → ℚ := fun r j => bordered X' pr pc r (col j)
    change ForwardBound rows V (n+1) A b prev
    rw [ForwardBound]
    refine ⟨⟨fun r j => hw r (col j),fun r => hw r rhs,hd⟩,?_⟩
    cases hscan : rows.find? (fun r => decide (A r 0 ≠ 0)) with
    | none => exact True.intro
    | some p =>
      have hp' : (fun r : I => decide (A r 0 ≠ 0)) p = true :=
        List.find?_some (p := fun r : I => decide (A r 0 ≠ 0)) (a := p) hscan
      have hp : A p 0 ≠ 0 := of_decide_eq_true hp'
      let pr' := push pr p
      let pc' := push pc (col 0)
      have ha : tailMatrix A p prev = fun r j => bordered X' pr' pc' r (col j.succ) := by
        funext r j
        exact ordered_bordered_div X' pr pc p r (col 0) (col j.succ) hprev
      have hb : tailRhs A b p prev = fun r => bordered X' pr' pc' r rhs := by
        funext r
        exact ordered_bordered_div X' pr pc p r (col 0) rhs hprev
      have hs : Fintype.card (K ⊕ Unit) + n + 1 ≤ N := by
        simp only [Fintype.card_sum, Fintype.card_unit]
        omega
      have hv (r c) : IntSized V (bordered X' pr' pc' r c) :=
        single_border_sized X pr' pc' r c T N hT hX (by omega)
      refine ⟨?_,?_⟩
      · constructor
        · intro r j
          apply exact_cross_from_integer_cells (hw p (col 0)) (hw r (col j.succ))
            (hw r (col 0)) (hw p (col j.succ)) hd hprev
          exact (show IntSized V (tailMatrix A p prev r j) from by rw [ha]; exact hv r _)
        · intro r
          apply exact_cross_from_integer_cells (hw p (col 0)) (hw r rhs)
            (hw r (col 0)) (hw p rhs) hd hprev
          exact (show IntSized V (tailRhs A b p prev r) from by rw [hb]; exact hv r rhs)
      · rw [ha,hb]
        exact forward_bordered rows T N X hT hX n pr' pc' (fun j => col j.succ) rhs hs hp
termination_by n

theorem bordered_empty {I J : Type*} (X : I → J → ℚ) (r : I) (c : J) :
    bordered X (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → J) r c = X r c := by
  letI : Unique (Fin 0 ⊕ Unit) :=
    ⟨⟨Sum.inr ()⟩, by
      rintro (i | ⟨⟩)
      · exact i.elim0
      · rfl⟩
  rw [bordered, Matrix.det_unique]
  rfl

theorem integer_table_actual_forward {I : Type*} (rows : List I) (T : ℕ)
    (n : ℕ) (A : I → Fin n → ℤ) (b : I → ℤ) (hT : 1 ≤ T)
    (hA : ∀ i j, (A i j).natAbs ≤ T) (hb : ∀ i, (b i).natAbs ≤ T) :
    ForwardBound rows (minorCap T (n+1)) n (fun i j => (A i j : ℚ))
      (fun i => (b i : ℚ)) 1 := by
  let X : I → Fin n ⊕ Unit → ℤ := fun i => Sum.elim (A i) (fun _ => b i)
  have hX (i j) : (X i j).natAbs ≤ T := by
    rcases j with (j|_)
    · exact hA i j
    · exact hb i
  have hh := forward_bordered rows T (n+1) X hT hX n (Fin.elim0 : Fin 0 → I)
    (Fin.elim0 : Fin 0 → (Fin n ⊕ Unit)) Sum.inl (.inr ())
    (by simp) (by rw [Matrix.det_isEmpty]; exact one_ne_zero)
  simp only [bordered_empty, Matrix.det_isEmpty] at hh
  exact hh

/-- The actual R59 normalized table, including its RHS, is the only width
input here. Every built cell and every update is then bounded and integral. -/
theorem cleared_actual_forward {I : Type*} (rows : List I) (allRows : ∀ i, i ∈ rows)
    {n B : ℕ} (A : I → Fin n → ℚ) (b : I → ℚ)
    (hA : ∀ i, ∀ j, inputHeight B (A i j)) (hb : ∀ i, inputHeight B (b i)) :
    let D := clearDen rows A b
    let L := B + B*((n+1)*rows.length)
    ForwardBound rows (minorCap (2^L) (n+1)) n
      (fun i j => (D : ℚ) * A i j) (fun i => (D : ℚ) * b i) 1 := by
  classical
  dsimp only
  let D := clearDen rows A b
  let L := B + B*((n+1)*rows.length)
  have hs (i : I) := actual_starting_integer_height rows A b
    (fun k _ => hA k) (fun k _ => hb k) i (allRows i)
  choose A' hA' using (fun i j => (hs i).1 j)
  choose b' hb' using (fun i => (hs i).2)
  have hq : ForwardBound rows (minorCap (2^L) (n+1)) n
      (fun i j => (A' i j : ℚ)) (fun i => (b' i : ℚ)) 1 :=
    integer_table_actual_forward rows (2^L) n A' b' (Nat.one_le_two_pow)
      (fun i j => (hA' i j).2) (fun i => (hb' i).2)
  change ForwardBound rows (minorCap (2^L) (n+1)) n
    (fun i j => (D : ℚ) * A i j) (fun i => (D : ℚ) * b i) 1
  have ha : (fun i j => (D : ℚ) * A i j) = fun i j => (A' i j : ℚ) := by
    funext i j
    exact (hA' i j).1
  have hh : (fun i => (D : ℚ) * b i) = fun i => (b' i : ℚ) := by
    funext i
    exact (hb' i).1
  rw [ha,hh]
  exact hq

#print axioms lifted_det
#print axioms exact_cross_from_integer_cells
#print axioms forward_bordered
#print axioms integer_table_actual_forward
#print axioms cleared_actual_forward

end J3R60
