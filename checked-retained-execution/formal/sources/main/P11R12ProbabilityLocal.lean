import P11R12Choice
import Mathlib.Tactic

/-! The real ordered-cell address chart depends only on its type's
mask. The permutation of any other ordered cell is not read. -/
namespace P11R12Probability
open scoped Classical BigOperators
open P11FullPacking P11R12Choice OuterNodePacking
variable {K : Type*} [LinearOrder K] {a b : ℕ}

def maskAt (k : Key (Fin a) K) (u : Orient k) (j : Key (Fin a) K) : Orient j :=
  if e : j=k then e.symm ▸ u else fun _ => false

@[simp] theorem maskAt_self (k : Key (Fin a) K) (u : Orient k) :
    maskAt k u k = u := by simp [maskAt]

abbrev LocalCell (b : ℕ) (k : Key (Fin a) K) (u c : Orient k) :=
  Σ _ : Packet b k, LocalFiber k u c

noncomputable def localAddress (b : ℕ) (k : Key (Fin a) K) (u c : Orient k) :
    LocalCell b k u c ≃ Fin (b*2^a) := by
  classical
  apply Fintype.equivOfCardEq
  rw [← Nat.card_eq_fintype_card,Fintype.card_fin]
  simpa [LocalCell,TypeCellFiber,commonMask] using
    (type_cell_card (b:=b) (commonMask (maskAt k u)) k c)

noncomputable def localEnds (b : ℕ) (k : Key (Fin a) K) (u c : Orient k) (right : Bool) :
    Finset (Fin (b*2^a)) :=
  Finset.univ.filter (fun q => ((localAddress b k u c).symm q).2.val = endpointIndex a right)

theorem localEnds_equal (m : ∀ j : Key (Fin a) K, Orient j)
    (k : Key (Fin a) K) (c : Orient k) (right : Bool) :
    endpointAddresses (b:=b) m k c right = localEnds b k (m k) c right := rfl

theorem localEnds_card (k : Key (Fin a) K) (u : Orient k) (right : Bool) :
    (localEnds b k u (GuardedPacking.endMask right u) right).card = b*2^Nat.card (Hot k) := by
  simpa only [localEnds_equal,maskAt_self] using
    (chosen_cell_end_count (b:=b) (maskAt k u) k right)

theorem localEnds_empty (k : Key (Fin a) K) (u c : Orient k) (right : Bool)
    (h : GuardedPacking.endMask right u ≠ c) :
    localEnds b k u c right = ∅ := by
  have h' : GuardedPacking.endMask right (maskAt k u k) ≠ c := by simpa only [maskAt_self]
  simpa only [localEnds_equal,maskAt_self] using
    (other_cell_has_no_end (b:=b) (maskAt k u) k c right h')

def endpointEvent (k : Key (Fin a) K) (c : Orient k) (x : Fin (b*2^a)) (right : Bool)
    (z : TypeDraw b k) : Prop :=
  z.2 c x ∈ localEnds b k z.1 c right

variable {W : Type*} [Fintype W]

noncomputable def realIndex (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (w : W) : Fin (b*2^a) :=
  initialIndex f cap (f w) ⟨w,rfl⟩

def realEvent (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (w : W) (right : Bool)
    (z : TypeDraw b (key (f w))) : Prop :=
  endpointEvent (key (f w)) (orientation (f w)) (realIndex f cap w) right z

theorem sampled_endpoint_is_local (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (w : W) (right : Bool) :
    (seat ω f cap w).2 = endpointIndex a right ↔ realEvent f cap w right (ω (key (f w))) := by
  rw [actual_endpoint_event,localEnds_equal]
  rfl

theorem sameCell_index_ne (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (w w' : W)
    (hc : f w=f w') (hn : w≠w') :
    realIndex f cap w ≠ realIndex f cap w' := by
  intro h
  have rightAt (c : Cell (Fin a) K) (hc' : f w'=c) :
      initialIndex f cap c ⟨w',hc'⟩ = realIndex f cap w' := by
    subst c
    rfl
  have h' : initialIndex f cap (f w) ⟨w,rfl⟩ =
      initialIndex f cap (f w) ⟨w',hc.symm⟩ := by
    rw [rightAt]
    exact h
  exact hn (congrArg Subtype.val ((initialIndex f cap (f w)).injective h'))

#print axioms localEnds_equal
#print axioms localEnds_card
#print axioms localEnds_empty
#print axioms sampled_endpoint_is_local
#print axioms sameCell_index_ne
end P11R12Probability
