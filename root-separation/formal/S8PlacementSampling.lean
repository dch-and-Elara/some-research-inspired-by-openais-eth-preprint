import S8Primitive
import S8Placement

namespace S8

set_option maxHeartbeats 600000

open scoped BigOperators
open SourceDensity

variable {W X Y LX LY I A : Type*}
  [Fintype W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype LX] [DecidableEq LX] [Fintype LY] [DecidableEq LY]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]

abbrev Primitive (X Y LX LY I : Type*) := I × ((X ⊕ LX) ⊕ (Y ⊕ LY))

instance primitiveDecEq (X Y LX LY I : Type*) [DecidableEq X] [DecidableEq Y]
    [DecidableEq LX] [DecidableEq LY] [DecidableEq I] :
    DecidableEq (Primitive X Y LX LY I) :=
  letI : DecidableEq (X ⊕ LX) := inferInstance
  letI : DecidableEq (Y ⊕ LY) := inferInstance
  letI : DecidableEq ((X ⊕ LX) ⊕ (Y ⊕ LY)) := inferInstance
  inferInstanceAs (DecidableEq (I × ((X ⊕ LX) ⊕ (Y ⊕ LY))))

def key {X L : Type*} (classify : X → Option L) (t i : I) (x : X) : X ⊕ L :=
  if i = t then (classify x).elim (.inl x) Sum.inr else .inl x

def site (left : W → X) (right : W → Y) (shareL : X → Option LX)
    (shareR : Y → Option LY) (t : I) (w : W) (q : Bool × I) : Primitive X Y LX LY I :=
  (q.2, if q.1 then .inr (key shareR t q.2 (right w)) else .inl (key shareL t q.2 (left w)))

def words (left : W → X) (right : W → Y) (shareL : X → Option LX)
    (shareR : Y → Option LY) (t : I) (ω : Primitive X Y LX LY I → A) (w : W) :
    (I → A) × (I → A) :=
  (fun i => ω (site left right shareL shareR t w (false,i)),
   fun i => ω (site left right shareL shareR t w (true,i)))

theorem collision_equiv {C D : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype D] [DecidableEq D] [Nonempty D] (e : C ≃ D) (cell : W → C) :
    collision (e ∘ cell) = collision cell := by
  simp only [collision_pair, Function.comp_apply, e.apply_eq_iff_eq, Fintype.card_congr e]

theorem mean_words (left : W → X) (right : W → Y) (shareL : X → Option LX)
    (shareR : Y → Option LY) (t : I) (bad : Finset (W × W))
    (good : ∀ e f, (e,f) ∉ bad →
      Function.Injective (Sum.elim (site left right shareL shareR t e)
        (site left right shareL shareR t f))) :
    (∑ ω : Primitive X Y LX LY I → A,
      ProductVariance.uniformWeight (Primitive X Y LX LY I → A) *
        collision (words left right shareL shareR t ω)) ≤ bad.card := by
  classical
  let toWords := (Equiv.curry Bool I A).trans (Equiv.boolArrowEquivProd (I → A))
  have h (ω : Primitive X Y LX LY I → A) : words left right shareL shareR t ω =
      toWords ∘ (fun w => ω ∘ site left right shareL shareR t w) := rfl
  simp only [h, collision_equiv]
  exact primitive_collision_bound _ bad good

theorem uniform_mass {T : Type*} [Fintype T] [Nonempty T] :
    (∑ _ : T, ProductVariance.uniformWeight T) = 1 := by
  simp only [ProductVariance.uniformWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def mainVariable {G : Type*} (ω : Primitive (V × Fin 4) Y Empty G I → A)
    (i : I) (v : V × Fin 4) : A := ω (i, Sum.inl (Sum.inl v))

theorem uniform_variable_moment {G : Type*} [Fintype G] [DecidableEq G] (i : I) :
    (∑ ω : Primitive (V × Fin 4) Y Empty G I → A,
      ProductVariance.uniformWeight (Primitive (V × Fin 4) Y Empty G I → A) *
        collision (mainVariable ω i)) ≤ Fintype.card (V × Fin 4) := by
  classical
  let bad := (Finset.univ : Finset (V × Fin 4)).map ⟨fun v => (v,v),
    fun _ _ hv => congrArg Prod.fst hv⟩
  have hb : bad.card = Fintype.card (V × Fin 4) := by simp [bad]
  rw [← hb]
  refine mean_collision_le _ uniform_mass (fun _ => by
    unfold ProductVariance.uniformWeight; positivity) _ bad ?_
  intro e f hef
  have hne : e ≠ f := by
    intro h
    subst f
    exact hef (by simp [bad])
  let eSite (_ : Unit) : Primitive (V × Fin 4) Y Empty G I := (i, .inl (.inl e))
  let fSite (_ : Unit) : Primitive (V × Fin 4) Y Empty G I := (i, .inl (.inl f))
  have inj : Function.Injective (Sum.elim eSite fSite) := by
    rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) h <;> simp_all [eSite, fSite, eq_comm]
  have heq (ω : Primitive (V × Fin 4) Y Empty G I → A) :
      ω ∘ eSite = ω ∘ fSite ↔ mainVariable ω i e = mainVariable ω i f := by
    simp [funext_iff, mainVariable, eSite, fSite]
  have h := primitive_agreement (A := A) eSite fSite inj
  simp only [heq, Fintype.card_fun, Fintype.card_unit, pow_one] at h
  exact h

end S8

#print axioms S8.collision_equiv
#print axioms S8.mean_words
#print axioms S8.uniform_variable_moment

