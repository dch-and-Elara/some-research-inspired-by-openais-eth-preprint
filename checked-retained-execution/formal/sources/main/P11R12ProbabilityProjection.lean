import P11R12ProbabilityLocal
import Mathlib.Tactic

/-! Restricting the uniform whole-type draw to its orientation mask and
one cell permutation discards only independent, unread coordinates. -/
namespace P11R12Probability
open scoped Classical BigOperators
open P11SourceGeometry PacketVariance RandomEndpoint
variable {U C P V : Type*}

noncomputable def uniform (A : Type*) [Fintype A] : A → ℚ :=
  fun _ => 1/(Fintype.card A:ℚ)

theorem uniform_prob (A : Type*) [Fintype A] [Nonempty A] : prob (uniform A) := by
  classical
  refine ⟨fun _ => ?_,?_⟩
  · unfold uniform
    positivity
  · simp [uniform,Finset.sum_const,nsmul_eq_mul]

def readCoord (c : C) (z : U × (C→P)) : U×P := (z.1,z.2 c)

theorem readCoord_surjective (c : C) : Function.Surjective (readCoord (U:=U) (P:=P) c) :=
  fun x => ⟨(x.1,fun _ => x.2),rfl⟩

theorem readCoord_fiber_same (c : C) (x y : U×P) :
    Nat.card {z // readCoord c z=x} = Nat.card {z // readCoord c z=y} := by
  classical
  let T : U×P ≃ U×P := (Equiv.swap x.1 y.1).prodCongr (Equiv.swap x.2 y.2)
  let F : (C→P) ≃ (C→P) :=
    Equiv.piCongrRight (fun i => if i=c then Equiv.swap x.2 y.2 else Equiv.refl _)
  let G : U × (C→P) ≃ U × (C→P) := (Equiv.swap x.1 y.1).prodCongr F
  have he (z : U × (C→P)) : readCoord c (G z) = T (readCoord c z) := by
    simp [readCoord,G,T,F]
  have ht : T x=y := by
    apply Prod.ext
    · exact Equiv.swap_apply_left _ _
    · exact Equiv.swap_apply_left _ _
  refine Nat.card_congr (Equiv.subtypeEquiv G (fun z => ?_))
  rw [he,← ht,T.injective.eq_iff]

theorem uniform_coordinate [Fintype U] [Fintype C] [Fintype P]
    [Nonempty U] [Nonempty P] (c : C) (event : U×P→Prop) :
    probability (uniform (U×(C→P))) (fun z => event (readCoord c z)) =
      probability (uniform (U×P)) event := by
  classical
  unfold uniform
  rw [uniform_event_card,uniform_event_card]
  exact uniform_fiber_fraction (readCoord c) (readCoord_surjective c) event (readCoord_fiber_same c)

theorem uniform_relabel [Fintype U] [Fintype V] (e : U≃V) (event : V→Prop) :
    probability (uniform U) (fun x => event (e x)) = probability (uniform V) event := by
  classical
  unfold uniform
  rw [uniform_event_card,uniform_event_card]
  rw [Nat.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl)),Nat.card_congr e]

#print axioms uniform_prob
#print axioms readCoord_fiber_same
#print axioms uniform_coordinate
#print axioms uniform_relabel
end P11R12Probability
