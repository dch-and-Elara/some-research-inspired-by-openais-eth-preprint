import P11R12ProbabilityLocal
import Mathlib.Tactic

/-! Endpoint membership and selected-port lists commute with restriction
of the sampled packing to one unordered type. -/
namespace P11R12Probability
open scoped Classical BigOperators
open P11FullPacking P11R12Choice OuterNodePacking
variable {K W : Type*} [LinearOrder K] [Fintype W] {a b : ℕ}

noncomputable def pickedLocal (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (side : W → Bool) (k : Key (Fin a) K)
    (z : TypeDraw b k) : Finset W :=
  Finset.univ.filter fun w =>
    ∃ h : key (f w)=k, realEvent f cap w (side w) (cast (congrArg (TypeDraw b) h.symm) z)

theorem picked_exact_local (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (side : W → Bool) (k : Key (Fin a) K) :
    P11R12Choice.picked ω f cap side k = pickedLocal f cap side k (ω k) := by
  ext w
  simp only [P11R12Choice.picked,pickedLocal,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [sampled_endpoint_is_local]
  constructor
  · rintro ⟨h,hW⟩
    subst k
    exact ⟨rfl,hW⟩
  · rintro ⟨h,hW⟩
    subst k
    exact ⟨rfl,hW⟩

omit [Fintype W] in
theorem same_key_same_column (c d : Cell (Fin a) K) (hk : key c=key d)
    (hc : ∀ i, (c i).2=(d i).2) : c=d := by
  funext i
  have hs : sortPair (c i)=sortPair (d i) :=
    congrArg (fun k : Key (Fin a) K => k.val i) hk
  have h := hc i
  generalize c i = x at hs h ⊢
  generalize d i = y at hs h ⊢
  rcases x with ⟨x,z⟩
  rcases y with ⟨y,z'⟩
  change z=z' at h
  subst z'
  by_cases hx : x≤z <;> by_cases hy : y≤z <;> simp [sortPair,hx,hy] at hs ⊢
  · exact hs
  · exact hs.1.trans hs.2
  · exact hs.2.trans hs.1
  · exact hs

theorem realEvent_at_cell (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (w : W) (right : Bool)
    (c : Cell (Fin a) K) (h : f w=c) (z : TypeDraw b (key c)) :
    realEvent f cap w right (cast (congrArg (fun d => TypeDraw b (key d)) h.symm) z) =
      endpointEvent (key c) (orientation c) (realIndex f cap w) right z := by
  subst c
  rfl

#print axioms picked_exact_local
#print axioms same_key_same_column
#print axioms realEvent_at_cell
end P11R12Probability
