import P11R12ProbabilityProjection
import Mathlib.Tactic

/-! Single-port and distinct-two-port marginal laws for the original
type-wise draw. They use the actual shared same-cell permutation. -/
namespace P11R12Probability
open scoped Classical BigOperators
open P11FullPacking P11R12Choice P11SourceGeometry RandomEndpoint
variable {K : Type*} [LinearOrder K] {a b : ℕ}

noncomputable def maskNumber (k : Key (Fin a) K) : Orient k ≃ Fin (2^Nat.card (Hot k)) := by
  classical
  apply Fintype.equivOfCardEq
  rw [← Nat.card_eq_fintype_card,Fintype.card_fin]
  change Nat.card (Hot k→Bool)=_
  rw [Nat.card_fun,Nat.card_eq_fintype_card (α:=Bool),Fintype.card_bool]

abbrev perm (a b : ℕ) := Equiv.Perm (Fin (b*2^a))

theorem uniform_eligible (k : Key (Fin a) K) (c q : Orient k) (event : perm a b → Prop) [DecidablePred event] :
    probability (uniform (TypeDraw b k)) (fun z => z.1=q ∧ event (z.2 c)) =
      (Nat.card {x : Fin (2^Nat.card (Hot k)) × perm a b //
          x.1=maskNumber k q ∧ event x.2}:ℚ) /
        (Nat.card (Fin (2^Nat.card (Hot k)) × perm a b):ℚ) := by
  classical
  letI : Nonempty (Orient k) := ⟨fun _ => false⟩
  letI : Nonempty (perm a b) := ⟨Equiv.refl _⟩
  let e : Orient k × perm a b ≃ Fin (2^Nat.card (Hot k)) × perm a b :=
    (maskNumber k).prodCongr (Equiv.refl _)
  unfold uniform
  rw [uniform_event_card]
  let P : Orient k × perm a b → Prop := fun x => x.1=q ∧ event x.2
  change ((Nat.card {z : TypeDraw b k // P (readCoord c z)}):ℚ) / _ = _
  rw [uniform_fiber_fraction (readCoord c) (readCoord_surjective c) P (readCoord_fiber_same c)]
  have he (x : Orient k × perm a b) : P x ↔
      (e x).1=maskNumber k q ∧ event (e x).2 := by simp [P,e]
  let et : {x : Orient k × perm a b // P x} ≃
      {x : Fin (2^Nat.card (Hot k)) × perm a b // x.1=maskNumber k q ∧ event x.2} :=
    Equiv.subtypeEquiv e he
  rw [Nat.card_congr et,Nat.card_congr e]

theorem event_eligible (k : Key (Fin a) K) (c : Orient k) (x : Fin (b*2^a)) (right : Bool)
    (z : TypeDraw b k) :
    endpointEvent k c x right z ↔
      z.1=GuardedPacking.endMask right c ∧
        z.2 c x ∈ localEnds b k (GuardedPacking.endMask right c) c right := by
  by_cases hu : z.1=GuardedPacking.endMask right c
  · simp [endpointEvent,hu]
  · have hd : GuardedPacking.endMask right z.1≠c := fun h =>
      hu (by rw [← h,GuardedPacking.endMask_involutive right z.1])
    simp [endpointEvent,localEnds_empty k z.1 c right hd,hu]

theorem uniform_single_endpoint (k : Key (Fin a) K) (c : Orient k)
    (x : Fin (b*2^a)) (right : Bool) (hb : 0<b) :
    probability (uniform (TypeDraw b k)) (endpointEvent k c x right) =
      1/((2^a:ℕ):ℚ) := by
  classical
  let q := GuardedPacking.endMask right c
  let E := localEnds b k q c right
  have hE : E.card=b*2^Nat.card (Hot k) := by
    have he := localEnds_card (b:=b) k q right
    rw [show GuardedPacking.endMask right q=c from GuardedPacking.endMask_involutive right c] at he
    exact he
  rw [event_congr (uniform (TypeDraw b k)) _ _ (event_eligible k c x right)]
  rw [uniform_eligible k c q (fun σ => σ x∈E)]
  exact physical_single_exact (maskNumber k q) x E hb (by positivity) hE

theorem uniform_same_cell_pair (k : Key (Fin a) K) (c : Orient k)
    (x y : Fin (b*2^a)) (hne : x≠y) (right : Bool) (hb : 0<b) (hH : 1<b*2^a) :
    (1-1/(b:ℚ))/((2^a:ℕ):ℚ)^2 ≤
      probability (uniform (TypeDraw b k))
        (fun z => endpointEvent k c x right z ∧ endpointEvent k c y right z) := by
  classical
  let q := GuardedPacking.endMask right c
  let E := localEnds b k q c right
  have hE : E.card=b*2^Nat.card (Hot k) := by
    have he := localEnds_card (b:=b) k q right
    rw [show GuardedPacking.endMask right q=c from GuardedPacking.endMask_involutive right c] at he
    exact he
  have he (z : TypeDraw b k) :
      (endpointEvent k c x right z ∧ endpointEvent k c y right z) ↔
        z.1=q ∧ z.2 c x∈E ∧ z.2 c y∈E := by
    rw [event_eligible,event_eligible]
    constructor
    · rintro ⟨⟨h,hx⟩,⟨_,hy⟩⟩
      exact ⟨h,hx,hy⟩
    · rintro ⟨h,hx,hy⟩
      exact ⟨⟨h,hx⟩,⟨h,hy⟩⟩
  rw [event_congr (uniform (TypeDraw b k)) _ _ he]
  rw [uniform_eligible k c q (fun σ => σ x∈E ∧ σ y∈E)]
  exact physical_sameType_lower (maskNumber k q) ⟨(x,y),hne⟩ E hb (by positivity) hH hE

#print axioms maskNumber
#print axioms uniform_eligible
#print axioms event_eligible
#print axioms uniform_single_endpoint
#print axioms uniform_same_cell_pair
end P11R12Probability
