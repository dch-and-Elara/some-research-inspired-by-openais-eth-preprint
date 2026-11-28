import Mathlib.LinearAlgebra.Quotient.Basic

/-! Arbitrary nonlinear decoders of linear observations, and actual adaptive
query trees. The full input module is essential. This file does not assume
that a structured CNF family is itself a module. -/

namespace ArbitraryDecoder

variable {R M U V : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup U] [Module R U]
  [AddCommGroup V] [Module R V]

theorem kernel_necessary (E : M →ₗ[R] U) (T : M →ₗ[R] V)
    (D : U → V) (hD : ∀ x, D (E x) = T x) :
    LinearMap.ker E ≤ LinearMap.ker T := by
  intro x hx
  change T x = 0
  have hx' : E x = 0 := hx
  rw [← hD x, hx']
  simpa only [map_zero] using hD 0

theorem same_fiber (E : M →ₗ[R] U) (T : M →ₗ[R] V)
    (h : LinearMap.ker E ≤ LinearMap.ker T) {x y : M} (he : E x = E y) :
    T x = T y := by
  have hk : x - y ∈ LinearMap.ker E := by
    change E (x - y) = 0
    rw [map_sub, he, sub_self]
  have ht : T (x - y) = 0 := h hk
  exact sub_eq_zero.mp (by simpa only [map_sub] using ht)

noncomputable def decoder (E : M →ₗ[R] U) (T : M →ₗ[R] V) (u : U) : V := by
  classical
  exact if h : ∃ x, E x = u then T (Classical.choose h) else 0

theorem decoder_correct (E : M →ₗ[R] U) (T : M →ₗ[R] V)
    (h : LinearMap.ker E ≤ LinearMap.ker T) (x : M) :
    decoder E T (E x) = T x := by
  classical
  have hx : ∃ y, E y = E x := ⟨x, rfl⟩
  rw [decoder, dif_pos hx]
  exact same_fiber E T h (Classical.choose_spec hx)

theorem arbitrary_decoder_iff (E : M →ₗ[R] U) (T : M →ₗ[R] V) :
    (∃ D : U → V, ∀ x, D (E x) = T x) ↔
      LinearMap.ker E ≤ LinearMap.ker T := by
  constructor
  · rintro ⟨D, hD⟩
    exact kernel_necessary E T D hD
  · intro h
    exact ⟨decoder E T, decoder_correct E T h⟩

theorem collision_obstruction (E : M →ₗ[R] U) (T : M →ₗ[R] V)
    (x : M) (he : E x = 0) (ht : T x ≠ 0) :
    ¬ ∃ D : U → V, ∀ y, D (E y) = T y := by
  rintro ⟨D, hD⟩
  exact ht (kernel_necessary E T D hD he)

/-- Linearity on the actual image, without an unjustified linear extension
to the full observation module. -/
noncomputable def imageDecoder (E : M →ₗ[R] U) (T : M →ₗ[R] V)
    (h : LinearMap.ker E ≤ LinearMap.ker T) : LinearMap.range E →ₗ[R] V where
  toFun u := decoder E T u
  map_add' u v := by
    rcases u.property with ⟨x, hx⟩
    rcases v.property with ⟨y, hy⟩
    change decoder E T (u.val + v.val) = decoder E T u.val + decoder E T v.val
    rw [← hx, ← hy, ← map_add, decoder_correct E T h,
      decoder_correct E T h, decoder_correct E T h, map_add]
  map_smul' a u := by
    rcases u.property with ⟨x, hx⟩
    change decoder E T (a • u.val) = a • decoder E T u.val
    rw [← hx, ← map_smul, decoder_correct E T h, decoder_correct E T h, map_smul]

theorem imageDecoder_correct (E : M →ₗ[R] U) (T : M →ₗ[R] V)
    (h : LinearMap.ker E ≤ LinearMap.ker T) (x : M) :
    imageDecoder E T h (E.rangeRestrict x) = T x := decoder_correct E T h x

/-- Each node selects its next query from the previous answer. This permits
arbitrary answer-dependent routing and arbitrary values at leaves. -/
inductive QueryTree (I U V : Type*) where
  | leaf (value : V)
  | ask (index : I) (next : U → QueryTree I U V)

namespace QueryTree

variable {I : Type*}

def run (Q : I → M →ₗ[R] U) : QueryTree I U V → M → V
  | .leaf v, _ => v
  | .ask i next, x => run Q (next (Q i x)) x

def zeroPath [Zero U] : QueryTree I U V → List I
  | .leaf _ => []
  | .ask i next => i :: zeroPath (next 0)

omit [AddCommGroup V] [Module R V] in
theorem same_zero_path (Q : I → M →ₗ[R] U) (tree : QueryTree I U V) (x : M)
    (h : ∀ i ∈ tree.zeroPath, Q i x = 0) : tree.run Q x = tree.run Q 0 := by
  induction tree with
  | leaf v => rfl
  | ask i next ih =>
    have hi : Q i x = 0 := h i (by simp [zeroPath])
    have hn : ∀ j ∈ (next 0).zeroPath, Q j x = 0 := by
      intro j hj
      exact h j (by simp only [zeroPath, List.mem_cons]; exact Or.inr hj)
    simpa only [run, hi, map_zero] using ih 0 hn

/-- The zero execution itself supplies a fixed nonadaptive kernel certificate.
No assumption about the decoder, routing functions, or fan-out is made. -/
theorem zero_path_certificate (Q : I → M →ₗ[R] U) (tree : QueryTree I U V)
    (T : M →ₗ[R] V) (correct : ∀ x, tree.run Q x = T x) (x : M)
    (h : ∀ i ∈ tree.zeroPath, Q i x = 0) : T x = 0 := by
  rw [← correct x, same_zero_path Q tree x h, correct 0, map_zero]

end QueryTree

#print axioms kernel_necessary
#print axioms same_fiber
#print axioms decoder_correct
#print axioms arbitrary_decoder_iff
#print axioms collision_obstruction
#print axioms imageDecoder_correct
#print axioms QueryTree.same_zero_path
#print axioms QueryTree.zero_path_certificate

end ArbitraryDecoder
