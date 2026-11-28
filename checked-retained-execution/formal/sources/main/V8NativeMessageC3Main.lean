import V8NativeMessageMatchCount
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace V8NativeMessage.C3
open scoped Classical BigOperators
open V8PooledRange
noncomputable section

variable {V E G J : Type*} [Fintype V] [Fintype G] [CommRing J]

/-- The actual binary direct switch extension: ¬A ∨ L_s(B).
The port arguments are the graph-fixed jets at a fixed private point. -/
def switch (s : Bool) (θ₁ θ₂ : J) : J :=
  1-θ₁*(1-(if s then θ₂ else 1-θ₂))

/-- The designated private points, already weighted and with their
sign-independent factors multiplied into 'fixed'. These tables are
graph-fixed; the signs appear at only the actual old switch clauses. -/
structure MainLists (b : G → ℕ) where
  owner : V → G
  fixed : ∀ g, Fin (b g) → J
  θ₁ : ∀ g, Fin (b g) → V → J
  θ₂ : ∀ g, Fin (b g) → V → J

variable {b : G → ℕ} (F : MainLists (V:=V) (J:=J) b)

def mainPoint (s : V → Bool) (g : G) (k : Fin (b g)) : J :=
  F.fixed g k * ∏ v : {v // F.owner v=g}, switch (s v.val) (F.θ₁ g k v.val) (F.θ₂ g k v.val)

omit [Fintype G] in
theorem mainPoint_local (s t : V → Bool) (g : G) (k : Fin (b g))
    (h : ∀ v, F.owner v=g → s v=t v) :
    mainPoint F s g k=mainPoint F t g k := by
  unfold mainPoint
  apply congrArg (F.fixed g k * ·)
  exact Finset.prod_congr rfl (fun v _ => by rw [h v.val v.property])

def mainCompleted (s : V → Bool) : J := ∏ g, ∑ k : Fin (b g), mainPoint F s g k

theorem fixed_choices (s : V → Bool) :
    mainCompleted F s = ∑ q : ((g : G) → Fin (b g)), ∏ g, mainPoint F s g (q g) :=
  Fintype.prod_sum (mainPoint F s)

def mainPart (T : Finset G) (s : V → Bool) (q : (g : G) → Fin (b g)) : J :=
  ∏ g∈T, mainPoint F s g (q g)

variable {G₀ : Graph V E} {m : ℕ} (P : Pairs G₀ m)

structure MainCross (T : Finset G) where
  left : ∀ j, F.owner (P.seat (j,false)) ∈ T
  right : ∀ j, F.owner (P.seat (j,true)) ∉ T

theorem real_main_choice_split (T : Finset G) (cross : MainCross F P T)
    (x y : Fin m → Bool) (q : (g : G) → Fin (b g)) :
    (∏ g, mainPoint F (activeSigns P x y) g (q g)) =
      mainPart F T (activeSigns P x (fun _ => false)) q *
      mainPart F Tᶜ (activeSigns P (fun _ => false) y) q := by
  rw [← Finset.prod_mul_prod_compl T (fun g => mainPoint F (activeSigns P x y) g (q g))]
  unfold mainPart
  apply congrArg₂ (· * ·)
  · refine Finset.prod_congr rfl (fun g hg => ?_)
    apply mainPoint_local
    intro v hv
    by_cases hh : v∈Set.range P.seat
    · obtain ⟨⟨j,jb⟩,rfl⟩ := hh
      cases jb
      · rw [activeSigns_left,activeSigns_left]
      · exact (cross.right j (hv ▸ hg)).elim
    · simp only [activeSigns,liftPairs_off P _ v hh]
  · refine Finset.prod_congr rfl (fun g hg => ?_)
    apply mainPoint_local
    intro v hv
    by_cases hh : v∈Set.range P.seat
    · obtain ⟨⟨j,jb⟩,rfl⟩ := hh
      cases jb
      · exact ((Finset.mem_compl.mp hg) (hv ▸ cross.left j)).elim
      · rw [activeSigns_right,activeSigns_right]
    · simp only [activeSigns,liftPairs_off P _ v hh]

theorem real_main_completion_split (T : Finset G) (cross : MainCross F P T)
    (x y : Fin m → Bool) :
    mainCompleted F (activeSigns P x y) =
      ∑ q : ((g : G) → Fin (b g)),
        mainPart F T (activeSigns P x (fun _ => false)) q *
        mainPart F Tᶜ (activeSigns P (fun _ => false) y) q := by
  rw [fixed_choices]
  exact Finset.sum_congr rfl (fun q _ => real_main_choice_split F P T cross x y q)

#print axioms mainPoint_local
#print axioms fixed_choices
#print axioms real_main_choice_split
#print axioms real_main_completion_split
end
end V8NativeMessage.C3