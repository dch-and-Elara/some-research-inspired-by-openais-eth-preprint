import PrecisionErasure

/-!
# Explicit polynomial expansions for genuinely linear protected bits

Each original row leg, after fixing all other bits, is a polynomial
affine form in independently summed common bits. The finite Atom
expansion is built here from the actual supports of its coefficient
polynomials; a support budget is not assumed separately.
-/

namespace J9R14LowPrecisionLinear
open scoped Classical BigOperators Polynomial
open Polynomial PrecisionErasure

noncomputable section
variable {U R : Type*} [Fintype U] [CommRing R]

structure Linear (U R : Type*) [Semiring R] where
  constant : R[X]
  byBit : U→R[X]

def Linear.value (f : Linear U R) (x : Finset U) : R[X] :=
  f.constant + ∑ u∈x, f.byBit u

def Linear.component (f : Linear U R) : Option U→R[X]
  | none => f.constant
  | some u => f.byBit u

abbrev Choices (f : Linear U R) := Σ u : Option U, ↥((f.component u).support)

def Linear.atom (f : Linear U R) (c : Choices f) : Atom U R :=
  ⟨c.1.elim ∅ (fun u => {u}),c.2.val,(f.component c.1).coeff c.2.val⟩

omit [Fintype U] in
theorem support_sum (p : R[X]) :
    (∑ j : ↥p.support, Polynomial.monomial j.val (p.coeff j.val)) = p := by
  rw [Finset.sum_coe_sort p.support (fun j : ℕ => Polynomial.monomial j (p.coeff j))]
  exact p.as_sum_support.symm

omit [Fintype U] in
theorem expand_component (f : Linear U R) (x : Finset U) (o : Option U) :
    (∑ j : ↥(f.component o).support,
      Polynomial.monomial (f.atom ⟨o,j⟩).order (atomValue (f.atom ⟨o,j⟩) x)) =
      (o.elim True (fun u => u∈x) |> fun B => if B then f.component o else 0) := by
  cases o with
  | none =>
    simpa only [Linear.atom,atomValue,Option.elim_none,Finset.empty_subset,if_true] using
      support_sum f.constant
  | some u =>
    by_cases hu : u∈x
    · simpa only [Linear.atom,atomValue,Option.elim_some,Finset.singleton_subset_iff,if_pos hu] using
        support_sum (f.byBit u)
    · simp [Linear.atom,atomValue,hu]

theorem expansion (f : Linear U R) (x : Finset U) :
    f.value x = ∑ c : Choices f, Polynomial.monomial (f.atom c).order (atomValue (f.atom c) x) := by
  let t (o : Option U) : R[X] := if o.elim True (fun u => u∈x) then f.component o else 0
  calc
    _ = f.constant + ∑ u : U, if u∈x then f.byBit u else 0 := by
      unfold Linear.value
      rw [← Finset.sum_filter]
      simp
    _ = ∑ o : Option U, t o := by
      rw [Fintype.sum_option]
      simp only [t,Option.elim_none,Option.elim_some,if_true,Linear.component]
    _ = _ := by
      rw [Fintype.sum_sigma]
      exact Finset.sum_congr rfl (fun o _ => (expand_component f x o).symm)

omit [Fintype U] in
theorem atom_support (f : Linear U R) (allow : ℕ)
    (h : allow=0 → ∀ u, (f.byBit u).coeff 0=0) (c : Choices f) :
    (f.atom c).bits.card≤allow+(f.atom c).order := by
  rcases c with ⟨o,j⟩
  cases o with
  | none => simp [Linear.atom]
  | some u =>
    change ({u}:Finset U).card≤allow+j.val
    rw [Finset.card_singleton]
    by_contra hh
    have ha : allow=0 := by omega
    have hj : j.val=0 := by omega
    have hn := Polynomial.mem_support_iff.mp j.property
    change (f.byBit u).coeff j.val≠0 at hn
    exact hn (by rw [hj,h ha u])

variable {F : Type*} [Fintype F]

def product (f : F→Linear U R) : R[X] :=
  ∑ x : Finset U, ∏ r : F, (f r).value x

theorem product_explicit (f : F→Linear U R) :
    product f = cubeProduct (fun r : F => (f r).atom) := by
  unfold product cubeProduct
  simp only [expansion]

theorem coeff_linear_product (f : F→Linear U R) (allow : F→ℕ) (k j : ℕ)
    (hSum : (∑ i,allow i)≤k)
    (h : ∀ i, allow i=0 → ∀ u, ((f i).byBit u).coeff 0=0) :
    (2:R)^(Fintype.card U-k-j) ∣ (product f).coeff j := by
  rw [product_explicit]
  exact coeff_support_dvd (fun i : F => (f i).atom) allow k j hSum
    (fun i c => atom_support (f i) (allow i) (h i) c)

theorem coeff_linear_sum {X : Type*} (X₀ : Finset X) (f : X→F→Linear U R)
    (w : X→R) (allow : X→F→ℕ) (k j : ℕ)
    (hSum : ∀ x∈X₀, (∑ i,allow x i)≤k)
    (h : ∀ x∈X₀, ∀ i, allow x i=0 → ∀ u, ((f x i).byBit u).coeff 0=0) :
    (2:R)^(Fintype.card U-k-j) ∣ (∑ x∈X₀, C (w x)*product (f x)).coeff j := by
  rw [Polynomial.finset_sum_coeff]
  apply Finset.dvd_sum
  intro x hx
  rw [Polynomial.coeff_C_mul]
  exact dvd_mul_of_dvd_right (coeff_linear_product (f x) (allow x) k j (hSum x hx) (h x hx)) _

/-- The projected powers of two come from explicit linear factors.
This theorem applies to every choice of extension-ring probe. -/
theorem erasure_linear_sum {S X : Type*} [CommRing S] (ψ : R→+*S) (z : S)
    (X₀ : Finset X) (f : X→F→Linear U R) (w : X→R) (allow : X→F→ℕ)
    (v k p : ℕ) (hp : p≤v+(Fintype.card U-k)) (hnil : (2:S)^p=0)
    (hSum : ∀ x∈X₀, (∑ i,allow x i)≤k)
    (h : ∀ x∈X₀, ∀ i, allow x i=0 → ∀ u, ((f x i).byBit u).coeff 0=0) :
    (2:S)^v*z^k*(∑ x∈X₀, C (w x)*product (f x)).eval₂ ψ (2*z)=0 := by
  have hh := (pow_dvd_pow (2:S) hp).trans
    (completed_slot_dvd ψ _ z (Fintype.card U) k v
      (fun j => coeff_linear_sum X₀ f w allow k j hSum h))
  rwa [hnil,zero_dvd_iff] at hh

#print axioms expansion
#print axioms atom_support
#print axioms coeff_linear_product
#print axioms coeff_linear_sum
#print axioms erasure_linear_sum

end
end J9R14LowPrecisionLinear
