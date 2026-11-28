import J6RecursiveOrientationLocal
import J6RecursivePortCube
import Mathlib.Tactic

/-! The actual two-sided literal J6 host. One old row per original
clause/equality vertex in each planted layer; the padding old rows
are negative unary and free unary, and every new column is one
binary subdivision equality. The two original incidence maps are
equivalences, so neither side omits nor duplicates a physical wire. -/
namespace J6OrientedHost
open P11FullPacking J6RecursiveOrientation J6RecursiveOrientationLocal
open scoped BigOperators

inductive Gate (d : ℕ) where
  | clause (sign : Fin d → Bool)
  | equal
  | free

def Gate.eval {d : ℕ} (g : Gate d) (y : Fin d → Bool) : Bool :=
  match g with
  | .clause sign => decide (∃ i, y i = sign i)
  | .equal => decide (∀ i j, y i = y j)
  | .free => true

structure Plant (V : Type*) (m q : ℕ) where
  degree : V → ℕ
  old : (v : V) → Gate (degree v)
  rowPort : (Σ v : V, Fin (degree v)) ≃ Fin m
  colPort : (Fin q × Bool) ≃ Fin m

variable {S V : Type*} [LinearOrder S] {a b m q l : ℕ}

abbrev Pad (w : Fin a → S) (m b l : ℕ) := J6PhysicalPacking.Pad (diagonal w) m b l
abbrev Wire (w : Fin a → S) (m b l : ℕ) := J6PhysicalPacking.Wire (diagonal w) m b l
abbrev Old (V : Type*) (w : Fin a → S) (m b l : ℕ) :=
  (V × Fin (2*l)) ⊕ (Pad w m b l × Bool)
abbrev New (w : Fin a → S) (m b l q : ℕ) :=
  (Fin q × Fin (2*l)) ⊕ Pad w m b l

def oldScope (T : Plant V m q) (w : Fin a → S) :
    Old V w m b l → Type
  | .inl (v,_) => Fin (T.degree v)
  | .inr _ => Unit

def rowPort (T : Plant V m q) (w : Fin a → S) :
    (v : Old V w m b l) → oldScope T w v → Wire w m b l
  | .inl (v,j),i => .inl (T.rowPort ⟨v,i⟩,j)
  | .inr padding,_ => .inr padding

def colPort (T : Plant V m q) (w : Fin a → S) :
    (v : New w m b l q) → Bool → Wire w m b l
  | .inl (v,j),i => .inl (T.colPort (v,i),j)
  | .inr p,i => .inr (p,i)

def rowTable (T : Plant V m q) (w : Fin a → S) :
    (v : Old V w m b l) → (oldScope T w v → Bool) → Bool
  | .inl (v,_),y => (T.old v).eval y
  | .inr (_,positive),y => if positive then true else !(y ())

def colTable (w : Fin a → S) (_ : New w m b l q) (y : Bool → Bool) : Bool :=
  decide (y false=y true)

def owner
    (w : Fin a → S) (i : Fin a) :
    Sum (Old V w m b l) (New w m b l q) → S
  | .inl (.inl _) => w i
  | .inl (.inr (p,_)) => (p.1 i).1
  | .inr (.inl _) => w i
  | .inr (.inr p) => (p.1 i).2

noncomputable def group (mask : MaskFamily a b S) (w : Fin a → S) (h : m≤b) (hL : 2*l=2^a)
    (i : Fin a) : Sum (Wire w m b l) (Wire w m b l) → S :=
  Sum.elim (fun p => (physicalCell mask (oriented mask w m l h hL p) i).1)
    (fun p => (physicalCell mask (oriented mask w m l h hL p) i).2)

theorem owner_exact (T : Plant V m q) (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m≤b) (hL : 2*l=2^a) (i : Fin a)
    (v : Sum (Old V w m b l) (New w m b l q))
    (j : J6RecursivePortCube.scopes (oldScope T w) (fun _ => Bool) v) :
    group mask w h hL i (J6RecursivePortCube.ports (rowPort T w) (colPort T w) v j) =
      owner w i v := by
  rcases v with (⟨v,jj⟩|⟨p,side⟩)|(⟨v,jj⟩|p)
  · change (physicalCell mask (oriented mask w m l h hL (.inl (T.rowPort ⟨v,j⟩,jj))) i).1 = w i
    rw [oriented_plant,diagonalSlot_cell]
    rfl
  · change (physicalCell mask (oriented mask w m l h hL (.inr (p,side))) i).1 = (p.1 i).1
    rw [oriented_padding_same_owner]
  · change (physicalCell mask (oriented mask w m l h hL (.inl (T.colPort (v,j),jj))) i).2 = w i
    rw [oriented_plant,diagonalSlot_cell]
    rfl
  · change (physicalCell mask (oriented mask w m l h hL (.inr (p,j))) i).2 = (p.1 i).2
    rw [oriented_padding_same_owner]

theorem local_exact (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m≤b) (hL : 2*l=2^a) (t : ℕ) (ht : t ≠ 0) (i : Fin a)
    (hv : padicValInt 2 (t:ℤ)=i.val) (p q : Wire w m b l)
    (hs : shifted mask w m l h hL t p=some q) :
    group mask w h hL i (.inl p) = group mask w h hL i (.inr q) :=
  shifted_local mask w m l h hL t ht i hv p q hs

#print axioms owner_exact
#print axioms local_exact
end J6OrientedHost
