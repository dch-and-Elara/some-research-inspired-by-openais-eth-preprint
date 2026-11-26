
import S11Literal
import S11Interpolation

namespace S11

variable {R V I J : Type*} [CommRing R]

/-- Group g can receive only the signs of unary vertices in g. The
    representative selection and all recursion below g are local to this input. -/
def childOnGroup {A : Type*} (group : V → Fin 64)
    (child : (g : Fin 64) → ({v // group v = g} → Bool) → A)
    (σ : V → Bool) (g : Fin 64) : A :=
  child g (fun v => σ v.val)

omit [CommRing R] in
theorem lift_group_local {A : Type*} (group : V → Fin 64)
    (child : (g : Fin 64) → ({v // group v = g} → Bool) → A)
    (lift : A → R) (σ τ : V → Bool) (g : Fin 64)
    (h : ∀ v, group v = g → σ v = τ v) :
    lift (childOnGroup group child σ g) = lift (childOnGroup group child τ g) := by
  have he : (fun v : {v // group v = g} => σ v.val) = (fun v => τ v.val) :=
    funext fun v => h v.val v.property
  unfold childOnGroup
  rw [he]

abbrev ModTwoPow (R : Type*) [CommRing R] (p : ℕ) :=
  R ⧸ Ideal.span ({(2 : R)^p} : Set R)

abbrev reduce (R : Type*) [CommRing R] (p : ℕ) : R →+* ModTwoPow R p :=
  Ideal.Quotient.mk _

/-- Lift each child result before multiplying. No additive or
    multiplicative property of the section is needed. -/
theorem lift_batch_residue (p : ℕ) (l : List Slot) (groups : List (Fin 64))
    (child : Slot → Fin 64 → ModTwoPow R p) (lifted : Slot → Fin 64 → R)
    (h : ∀ b g, reduce R p (lifted b g) = child b g) :
    reduce R p (runBatch groups lifted l).1 = (runBatch groups child l).1 := by
  rw [runBatch_value, runBatch_value, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_inj_left.mpr
  intro b _
  rw [Function.comp_apply, map_list_prod, List.map_map]
  apply congrArg List.prod
  exact List.map_inj_left.mpr (fun g _ => h b g)

theorem lift_batch_error (p : ℕ) (l : List Slot) (groups : List (Fin 64))
    (child : Slot → Fin 64 → ModTwoPow R p) (lifted : Slot → Fin 64 → R)
    (h : ∀ b g, reduce R p (lifted b g) = child b g) (sample : R)
    (hidentity : (runBatch groups child l).1 = reduce R p sample) :
    ∃ e : R, (runBatch groups lifted l).1 = sample + 2^p * e := by
  have hmod := (lift_batch_residue p l groups child lifted h).trans hidentity
  have hm := (Ideal.Quotient.eq.1 hmod)
  obtain ⟨e,he⟩ := Ideal.mem_span_singleton.1 hm
  exact ⟨e, sub_eq_iff_eq_add'.1 he⟩

/-- Finite bit margin after the two published loss bounds. -/
theorem tapered_loss_fits (p M a u L : ℕ) (t : ℤ) :
    p + 6 * taper M u * (L / 2^level t) + 4 * M * (a+1) ≤ precision p M a u L t := by
  unfold precision
  have h1 : 6 * taper M u * (L / 2^level t) ≤ 8 * taper M u * (L / 2^level t) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  have h2 : 4 * M * (a+1) ≤ 8 * M * (a+1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  omega

#print axioms lift_group_local
#print axioms lift_batch_residue
#print axioms lift_batch_error
#print axioms tapered_loss_fits

end S11

