import F5R60OccurrenceCycle
import F5R59ConflictCore
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-! An actual ordered preprocessing cycle, built by filtering the input
position indices by name and cycling in increasing order. No arbitrary
cycle certificate, labels, or cycle-edge list is supplied. -/
namespace F5R61.Preprocess
set_option autoImplicit false
set_option warningAsError true
open F5R59

variable {C V : Type} {n : ℕ}

abbrev Name (S : ClauseSystem C V) (x : Vertex S) : V := (term S x).var
abbrev Fibre (S : ClauseSystem C V) (v : V) := {x : Vertex S // Name S x = v}

def initialOrder {m : ℕ} (S : ClauseSystem (Fin m) V) (width3 : ∀ c, S.width c = 3) :
    Fin (m * 3) ≃ Vertex S :=
  finProdFinEquiv.symm.trans (Equiv.sigmaEquivProdOfEquiv (fun c => finCongr (width3 c))).symm

variable [DecidableEq V]
variable (S : ClauseSystem C V) (e : Fin n ≃ Vertex S)

def sameIndices (v : V) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Name S (e i) = v)

@[simp] theorem mem_sameIndices (v : V) (i : Fin n) :
    i ∈ sameIndices S e v ↔ Name S (e i) = v := by
  simp [sameIndices]

def indexFibre (v : V) : Fibre S v ≃ {i : Fin n // i ∈ sameIndices S e v} where
  toFun x := ⟨e.symm x.val, (mem_sameIndices S e _ _).2 ((congrArg (Name S) (e.apply_symm_apply x.val)).trans x.property)⟩
  invFun i := ⟨e i.val, (mem_sameIndices S e _ _).1 i.property⟩
  left_inv x := Subtype.ext (e.apply_symm_apply x.val)
  right_inv i := Subtype.ext (e.symm_apply_apply i.val)

def fibreOrder (v : V) : Fin (sameIndices S e v).card ≃ Fibre S v :=
  ((sameIndices S e v).orderIsoOfFin rfl).toEquiv.trans (indexFibre S e v).symm

/-- Increase a bounded rank, wrapping the last one to zero. The inverse
implements the preceding rank, not a chosen permutation witness. -/
def rotation (k : ℕ) : Equiv.Perm (Fin k) where
  toFun i := if hi : i.val+1<k then ⟨i.val+1,hi⟩ else ⟨0,by have := i.isLt; omega⟩
  invFun i := if hi : 0<i.val then ⟨i.val-1,by have := i.isLt; omega⟩ else
    ⟨k-1,by have := i.isLt; omega⟩
  left_inv i := by
    dsimp only
    have bound := i.isLt
    by_cases hn : i.val+1<k
    · rw [dif_pos hn]
      have positive : 0<i.val+1 := by omega
      rw [dif_pos positive]
      apply Fin.ext
      change i.val+1-1=i.val
      omega
    · rw [dif_neg hn]
      have nonpositive : ¬ (0:ℕ)<0 := by omega
      rw [dif_neg nonpositive]
      apply Fin.ext
      change k-1=i.val
      omega
  right_inv i := by
    dsimp only
    have bound := i.isLt
    by_cases hp : 0<i.val
    · rw [dif_pos hp]
      have step : i.val-1+1<k := by omega
      rw [dif_pos step]
      apply Fin.ext
      change i.val-1+1=i.val
      omega
    · rw [dif_neg hp]
      have step : ¬ k-1+1<k := by omega
      rw [dif_neg step]
      apply Fin.ext
      change 0=i.val
      omega

theorem rotation_next {k : ℕ} (i : Fin k) (h : i.val+1<k) :
    rotation k i = ⟨i.val+1,h⟩ := dif_pos h

theorem rotation_wrap {k : ℕ} (i : Fin k) (h : ¬i.val+1<k) :
    rotation k i = ⟨0,by have := i.isLt; omega⟩ := dif_neg h

def localCycle (v : V) : Equiv.Perm (Fibre S v) :=
  let b := fibreOrder S e v
  b.symm.trans ((rotation _).trans b)

def successor : Equiv.Perm (Vertex S) :=
  let u := Equiv.sigmaFiberEquiv (Name S)
  u.symm.trans ((Equiv.sigmaCongrRight (fun v => localCycle S e v)).trans u)

theorem next_same_name (x : Vertex S) : Name S (successor S e x) = Name S x :=
  (localCycle S e (Name S x) ⟨x,rfl⟩).property

theorem next_at_rank (v : V) (i : Fin (sameIndices S e v).card) :
    successor S e (fibreOrder S e v i).val =
      (fibreOrder S e v (rotation _ i)).val := by
  let u := Equiv.sigmaFiberEquiv (Name S)
  have h : u ⟨v, fibreOrder S e v i⟩ = (fibreOrder S e v i).val := rfl
  rw [← h]
  unfold successor
  change (Equiv.sigmaFiberEquiv (Name S)) ((Equiv.sigmaCongrRight (fun v => localCycle S e v))
    ((Equiv.sigmaFiberEquiv (Name S)).symm (u ⟨v, fibreOrder S e v i⟩))) = _
  change u ((Equiv.sigmaCongrRight (fun v => localCycle S e v)) (u.symm (u ⟨v, fibreOrder S e v i⟩))) = _
  rw [u.symm_apply_apply]
  change (fibreOrder S e v (rotation _ ((fibreOrder S e v).symm (fibreOrder S e v i)))).val = _
  rw [Equiv.symm_apply_apply]

def active (x : Vertex S) : Prop :=
  2 ≤ (sameIndices S e (Name S x)).card

instance activeDec (x : Vertex S) : Decidable (active S e x) :=
  inferInstanceAs (Decidable (2 ≤ (sameIndices S e (Name S x)).card))

private theorem rotation_moves {k : ℕ} (size : 2 ≤ k) (i : Fin k) :
    rotation k i ≠ i := by
  intro eq
  by_cases hi : i.val+1<k
  · rw [rotation_next i hi] at eq
    have ee := congrArg Fin.val eq
    change i.val+1=i.val at ee
    omega
  · rw [rotation_wrap i hi] at eq
    have ee := congrArg Fin.val eq
    change 0=i.val at ee
    omega

theorem active_next_ne (x : Vertex S) (h : active S e x) : successor S e x ≠ x := by
  let b := fibreOrder S e (Name S x)
  let i := b.symm ⟨x,rfl⟩
  have hi : (b i).val = x := congrArg Subtype.val (b.apply_symm_apply ⟨x,rfl⟩)
  have nxt := next_at_rank S e (Name S x) i
  have hv : 2 ≤ (sameIndices S e (Name S x)).card := h
  intro eq
  have fixed : (b (rotation _ i)).val = (b i).val :=
    nxt.symm.trans ((congrArg (successor S e) hi).trans (eq.trans hi.symm))
  exact rotation_moves hv i (b.injective (Subtype.ext fixed))

private def walk {k : ℕ} : (d a : ℕ) → a+d<k → List (Fin k)
  | 0, _, _ => []
  | d+1, a, h => ⟨a+1,by omega⟩ :: walk d (a+1) (by omega)

private theorem walk_chain {k : ℕ} (b : Fin k → Bool)
    (hi : ∀ i, F5R60.Imp (b i) (b (rotation k i)))
    (d a : ℕ) (h : a+d<k) :
    F5R60.Chain b ⟨a,by omega⟩ (walk d a h) ⟨a+d,h⟩ := by
  induction d generalizing a with
  | zero => rfl
  | succ d ih =>
    change F5R60.Imp (b ⟨a,by omega⟩) (b ⟨a+1,by omega⟩) ∧
      F5R60.Chain b ⟨a+1,by omega⟩ (walk d (a+1) (by omega)) ⟨a+(d+1),h⟩
    constructor
    · have ei : rotation k ⟨a,by omega⟩ = ⟨a+1,by omega⟩ := by
        exact rotation_next (⟨a,by omega⟩ : Fin k) (by change a+1<k; omega)
      simpa only [ei] using hi ⟨a,by omega⟩
    · have hh := ih (a+1) (by omega)
      have ee : (⟨a+1+d,by omega⟩ : Fin k) = ⟨a+(d+1),h⟩ :=
        Fin.ext (by change a+1+d=a+(d+1); omega)
      rwa [← ee]

private theorem walk_mem {k : ℕ} (d a : ℕ) (h : a+d<k) (i : Fin k)
    (beg : a<i.val) (last : i.val≤a+d) : i∈walk d a h := by
  induction d generalizing a with
  | zero => omega
  | succ d ih =>
    change i ∈ (⟨a+1,by omega⟩ : Fin k) :: walk d (a+1) (by omega)
    by_cases eq : i.val=a+1
    · exact List.mem_cons.mpr (Or.inl (Fin.ext eq))
    · exact List.mem_cons.mpr (Or.inr (ih (a+1) (by omega) (by omega) (by omega)))

theorem ordered_rotation_all_equal {k : ℕ} (b : Fin k → Bool)
    (hi : ∀ i, F5R60.Imp (b i) (b (rotation k i))) (i j : Fin k) : b i=b j := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ m =>
    have endToFirst : F5R60.Imp (b ⟨m,by omega⟩) (b ⟨0,by omega⟩) := by
      have wrap : rotation (m+1) ⟨m,by omega⟩ = ⟨0,by omega⟩ :=
        rotation_wrap _ (by simp)
      simpa only [wrap] using hi ⟨m,by omega⟩
    have hc : F5R60.ClosedCycle b ⟨0,by omega⟩ (walk m 0 (by omega)) ⟨m,by omega⟩ :=
      ⟨by simpa only [Nat.zero_add] using walk_chain b hi m 0 (by omega), endToFirst⟩
    have all (j : Fin (m+1)) : b j = b ⟨0,by omega⟩ := by
      apply F5R60.actual_cycle_forces_equal b _ hc
      by_cases e : j.val=0
      · exact List.mem_cons.mpr (Or.inl (Fin.ext e))
      · exact List.mem_cons.mpr (Or.inr (walk_mem m 0 (by omega) j (by omega) (by omega)))
    exact (all i).trans (all j).symm

theorem active_cycles_force_one_value (b : Vertex S → Bool)
    (h : ∀ x, active S e x → F5R60.Imp (b x) (b (successor S e x)))
    {x y : Vertex S} (names : Name S x = Name S y) : b x = b y := by
  let v := Name S x
  let E := fibreOrder S e v
  let i := E.symm ⟨x,rfl⟩
  let j := E.symm ⟨y,names.symm⟩
  have hx : (E i).val = x := congrArg Subtype.val (E.apply_symm_apply ⟨x,rfl⟩)
  have hy : (E j).val = y := congrArg Subtype.val (E.apply_symm_apply ⟨y,names.symm⟩)
  rw [← hx,← hy]
  by_cases enough : 2 ≤ (sameIndices S e v).card
  · apply ordered_rotation_all_equal (fun i => b (E i).val)
    intro k
    have hactive : active S e (E k).val := by
      unfold active
      rw [(E k).property]
      exact enough
    simpa only [E,next_at_rank] using h (E k).val hactive
  · have eq : i=j := Fin.ext (by have p := i.isLt; have q := j.isLt; omega)
    rw [eq]

#print axioms initialOrder
#print axioms rotation
#print axioms fibreOrder
#print axioms successor
#print axioms next_same_name
#print axioms next_at_rank
#print axioms active_next_ne
#print axioms ordered_rotation_all_equal
#print axioms active_cycles_force_one_value
end F5R61.Preprocess
