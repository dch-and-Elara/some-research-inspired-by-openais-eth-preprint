import P5HybridClosureConditional

/-! Local conditional scores for actual four-word agreements with arbitrary
preassigned primitive keys. Correlated words are not averaged independently. -/
namespace Paper5.HybridSameRouteConditioning
open scoped BigOperators Classical
open GuardExpectation

set_option autoImplicit false
set_option warningAsError true

variable {P I A E : Type*} [Fintype P] [DecidableEq P] [Fintype I] [Fintype A]

def cell (keys : E → Bool → I → P) (z : P → A) (e : E) : (I → A) × (I → A) :=
  (fun i => z (keys e false i), fun i => z (keys e true i))

def pairKeys (keys : E → Bool → I → P) (e f : E) : Bool × Bool × I → P :=
  fun x => keys (if x.1 then f else e) x.2.1 x.2.2

noncomputable def support (keys : E → Bool → I → P) (e f : E) : Finset P :=
  Finset.univ.image (pairKeys keys e f)

noncomputable def restrictCell (keys : E → Bool → I → P) (e f : E)
    (z : support keys e f → A) (side : Bool) : (I → A) × (I → A) :=
  (fun i => z ⟨pairKeys keys e f (side,false,i),
      Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩,
   fun i => z ⟨pairKeys keys e f (side,true,i),
      Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩)

omit [Fintype P] [Fintype A] in
theorem support_le (keys : E → Bool → I → P) (e f : E) :
    (support keys e f).card ≤ 4 * Fintype.card I := by
  have h := Finset.card_image_le (s := (Finset.univ : Finset (Bool × Bool × I)))
    (f := pairKeys keys e f)
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_bool] at h
  unfold support
  omega

omit [Fintype P] in
theorem score_enumeration_le (keys : E → Bool → I → P) (e f : E)
    (hA : 0 < Fintype.card A) :
    Fintype.card (support keys e f → A) ≤ (Fintype.card A ^ (2 * Fintype.card I)) ^ 2 := by
  rw [Fintype.card_fun, Fintype.card_coe, ←pow_mul]
  have h := support_le keys e f
  apply Nat.pow_le_pow_right hA
  omega

theorem agreement_exact (keys : E → Bool → I → P) (e f : E)
    (w : P → A → ℚ) (hw : ∀ p, ∑ a,w p a=1) :
    average w (fun z => J1MainSourceCollision.indicator (cell keys z e = cell keys z f)) =
      average (fun i : support keys e f => w i)
        (fun z => J1MainSourceCollision.indicator
          (restrictCell keys e f z false = restrictCell keys e f z true)) := by
  exact Paper5.HybridClosure.average_on_support (support keys e f) w hw
    (fun z => J1MainSourceCollision.indicator
      (restrictCell keys e f z false = restrictCell keys e f z true))

end Paper5.HybridSameRouteConditioning
#print axioms Paper5.HybridSameRouteConditioning.support_le
#print axioms Paper5.HybridSameRouteConditioning.score_enumeration_le
#print axioms Paper5.HybridSameRouteConditioning.agreement_exact
