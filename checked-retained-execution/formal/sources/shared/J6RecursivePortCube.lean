import J6RecursiveAssembly
import J6NativeHeightResidue
import Mathlib.Tactic

/-! Retained tables on the literal old row / subdivision column scopes
give exactly the two Boolean factors of the J6 residue contraction.
This connects the typed child partition to the R6 height interface. -/
namespace J6RecursivePortCube
open scoped BigOperators
open J6RecursiveAssembly J6NativeHeightResidue
universe u
variable {R P V W : Type*} [CommRing R] [Fintype P] [DecidableEq P] [Fintype V] [Fintype W]

def scopes (row : V → Type u) (col : W → Type u) : Sum V W → Type u :=
  Sum.elim row col

def ports {row : V → Type u} {col : W → Type u}
    (left : ∀ v, row v → P) (right : ∀ w, col w → P) :
    ∀ g, scopes row col g → Sum P P
  | .inl v => fun i => .inl (left v i)
  | .inr w => fun i => .inr (right w i)

def flag {row : V → Type u} {col : W → Type u}
    (A : ∀ v, (row v → Bool) → Bool) (B : ∀ w, (col w → Bool) → Bool) :
    ∀ g, (scopes row col g → Bool) → Bool
  | .inl v => A v
  | .inr w => B w

noncomputable def good {T : Type*} [Fintype T] (a : T → Bool) : Bool := by
  classical
  exact decide (∀ v, a v=true)

theorem prod_flags {T : Type*} [Fintype T] (a : T → Bool) :
    (∏ v : T, if a v then (1:R) else 0) = if good a then 1 else 0 := by
  classical
  by_cases ha : ∀ v, a v=true
  · simp [ha,good]
  · push_neg at ha
    obtain ⟨v,hv⟩ := ha
    have hn : ¬ ∀ v, a v=true := fun h => hv (h v)
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])]
    simp [good,hn]

def pairIso : ((P→Bool) × (P→Bool)) ≃ (Sum P P→Bool) where
  toFun p := Sum.elim p.1 p.2
  invFun x := (fun p => x (.inl p),fun p => x (.inr p))
  left_inv _ := rfl
  right_inv _ := funext fun p => by cases p <;> rfl

theorem whole_eq_residueSlot {row : V → Type u} {col : W → Type u}
    (left : ∀ v, row v → P) (right : ∀ w, col w → P)
    (A : ∀ v, (row v → Bool) → Bool) (B : ∀ w, (col w → Bool) → Bool)
    (shift : P → Option P) (c : R) :
    wholeContraction (scopes row col) (ports left right)
        (fun v y => if flag A B v y then (1:R) else 0) shift c =
      residueSlot
        (fun y => good (fun v => A v (fun i => y (left v i))))
        (fun x => good (fun w => B w (fun i => x (right w i))))
        (fun p x => ((shift p).map x).getD false) c := by
  classical
  unfold wholeContraction residueSlot
  let kernel (a : (P → Bool) × (P → Bool)) : R :=
    if good (fun v => A v (fun i => a.1 (left v i))) &&
      good (fun w => B w (fun i => a.2 (right w i))) then
      ∏ p, ringEntry c (a.1 p) ((shift p).map a.2 |>.getD false)
    else 0
  change _ = ∑ y : P → Bool, ∑ x : P → Bool, kernel (y,x)
  rw [← Fintype.sum_prod_type kernel]
  symm
  apply Fintype.sum_equiv pairIso
  rintro ⟨y,x⟩
  rw [Fintype.prod_sum_type]
  change (if good (fun v => A v (fun i => y (left v i))) &&
    good (fun w => B w (fun i => x (right w i))) then
    ∏ p, ringEntry c (y p) ((shift p).map x |>.getD false) else 0) =
    ((∏ v, if A v (fun i => y (left v i)) then 1 else 0) *
      (∏ w, if B w (fun i => x (right w i)) then 1 else 0)) *
      ∏ p, LiteralPortCompiler.affine (y p) (value c ((shift p).map x |>.getD false))
  rw [prod_flags,prod_flags]
  have he (p : P) : ringEntry c (y p) ((shift p).map x |>.getD false) =
      LiteralPortCompiler.affine (y p) (value c ((shift p).map x |>.getD false)) := by
    cases y p <;> simp [ringEntry,LiteralPortCompiler.affine,value]
  simp_rw [he]
  cases good (fun v => A v (fun i => y (left v i))) <;>
    cases good (fun w => B w (fun i => x (right w i))) <;> simp

#print axioms prod_flags
#print axioms whole_eq_residueSlot
end J6RecursivePortCube
