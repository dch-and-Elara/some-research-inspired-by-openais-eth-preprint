import P5LiteralJets
import P5CyclicLength

/-! The scalar in §3.3. Quotienting the actual jet by its linear
multiplication image really substitutes the root by the negative
uniformizer; this construction gives both algebra maps. -/
namespace Paper5.ObservationExamples
open Polynomial
open scoped Polynomial

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 4200

noncomputable section
variable {S : Type*} [CommRing S]
abbrev Jet (S : Type*) [CommRing S] (k : ℕ) := AdjoinRoot ((X:S[X])^k)
abbrev jvar (S : Type*) [CommRing S] (k : ℕ) : Jet S k := AdjoinRoot.root ((X:S[X])^k)

def relation (a : S) (k : ℕ) : Ideal (Jet S k) :=
  Ideal.span ({jvar S k+(algebraMap S (Jet S k)) a}:Set (Jet S k))

abbrev SubstitutedJet (a : S) (k : ℕ) := Jet S k ⧸ relation a k
abbrev CoeffQuot (a : S) (k : ℕ) := S ⧸ Ideal.span ({a^k}:Set S)

theorem root_power_is_zero (k : ℕ) : (jvar S k)^k=0 := by
  simpa only [Polynomial.eval₂_pow,Polynomial.eval₂_X] using
    AdjoinRoot.eval₂_root ((X:S[X])^k)

theorem projected_root_is_negative (a : S) (k : ℕ) :
    Ideal.Quotient.mk (relation a k) (jvar S k) =
      -algebraMap S (SubstitutedJet a k) a := by
  let q := Ideal.Quotient.mk (relation a k)
  have h : q (jvar S k+(algebraMap S (Jet S k)) a)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [map_add] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem kills_singleton {A B : Type*} [CommRing A] [CommRing B]
    (f : A→+*B) (p : A) (hp : f p=0) :
    ∀ z : A,z∈Ideal.span ({p}:Set A) → f z=0 := by
  intro z hz
  obtain ⟨u,hu⟩ := Ideal.mem_span_singleton.mp hz
  rw [hu,map_mul,hp,zero_mul]

def scalar_substitution (a : S) (k : ℕ) : SubstitutedJet a k ≃ₐ[S] CoeffQuot a k := by
  let I := relation a k
  let q := Ideal.Quotient.mk I
  let y : (CoeffQuot a k) := -(algebraMap S (CoeffQuot a k)) a
  have ha : ((algebraMap S (CoeffQuot a k)) a)^k=0 := by
    rw [←map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hy : Polynomial.aeval y ((X:S[X])^k)=0 := by
    rw [map_pow,Polynomial.aeval_X]
    dsimp only [y]
    rw [neg_pow,ha,mul_zero]
  let H : Jet S k→ₐ[S] (CoeffQuot a k) := AdjoinRoot.liftHom ((X:S[X])^k) y hy
  have hHroot : H (jvar S k)=y := AdjoinRoot.liftHom_root ((X:S[X])^k) hy
  have hH : H (jvar S k+(algebraMap S (Jet S k)) a)=0 := by
    rw [map_add,hHroot,H.commutes]
    exact neg_add_cancel _
  let F : SubstitutedJet a k→ₐ[S] (CoeffQuot a k) :=
    Ideal.Quotient.liftₐ I H (kills_singleton H.toRingHom _ hH)
  have hf : F (q (jvar S k))=y := by
    change Ideal.Quotient.lift I H.toRingHom _ (Ideal.Quotient.mk I (jvar S k))=y
    rw [Ideal.Quotient.lift_mk]
    exact hHroot
  have hqpow : (q (jvar S k))^k=0 := by
    rw [←map_pow,root_power_is_zero,map_zero]
  have hqa : ((algebraMap S (SubstitutedJet a k)) a)^k=0 := by
    have h : -(q (jvar S k))=(algebraMap S (SubstitutedJet a k)) a := by
      rw [projected_root_is_negative,neg_neg]
    rw [←h,neg_pow,hqpow,mul_zero]
  let G : (CoeffQuot a k)→ₐ[S] SubstitutedJet a k :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId S (SubstitutedJet a k))
      (kills_singleton (algebraMap S (SubstitutedJet a k)) (a^k) (by rw [map_pow,hqa]))
  have gf : G.comp F = AlgHom.id S (SubstitutedJet a k) := by
    apply Ideal.Quotient.algHom_ext S
    apply AdjoinRoot.algHom_ext
    change G (F (q (jvar S k))) = q (jvar S k)
    rw [hf]
    change G (-(algebraMap S (CoeffQuot a k)) a)=_
    rw [map_neg,G.commutes,projected_root_is_negative]
  have fg : F.comp G = AlgHom.id S (CoeffQuot a k) := by
    apply Ideal.Quotient.algHom_ext S
    exact AlgHom.ext fun z => (F.comp G).commutes z
  have left : Function.LeftInverse G F := fun z=>DFunLike.congr_fun gf z
  have right : Function.RightInverse G F := fun z=>DFunLike.congr_fun fg z
  exact AlgEquiv.ofBijective F ⟨left.injective,right.surjective⟩

#print axioms root_power_is_zero
#print axioms projected_root_is_negative
#print axioms scalar_substitution
end
end Paper5.ObservationExamples
