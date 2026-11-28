import MainIncidence
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Basic

/-! Exact scalarization of one completed finite-algebra register.  A single
linear readout of a product of two local algebra-valued functions needs at most
the algebra dimension in scalar separated terms.  It is not necessary to
materialize all coefficient compositions of the original many-factor product.
-/

namespace FiniteAlgebraReadout

open scoped BigOperators
open Module

variable {K A J : Type*} [Field K] [CommRing A] [Algebra K A] [Fintype J]

theorem readout_mul (b : Basis J K A) (read : A →ₗ[K] K) (u v : A) :
    read (u * v) = ∑ j, b.repr u j * read (b j * v) := by
  conv_lhs => rw [← b.sum_repr u]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One linear readout after two sides have completed their products in A. -/
structure LocalReadout where
  side : Finset V
  left : (side → Bool) → A
  right : ((sideᶜ : Finset V) → Bool) → A
  read : A →ₗ[K] K

namespace LocalReadout

def value (t : LocalReadout (V:=V) (K:=K) (A:=A)) (σ : V → Bool) : K :=
  t.read (t.left (SeparatedRank.CutTerm.restrict t.side σ) *
    t.right (SeparatedRank.CutTerm.restrict t.sideᶜ σ))

noncomputable def scalarTerm (t : LocalReadout (V:=V) (K:=K) (A:=A))
    (b : Basis J K A) (j : J) : SeparatedRank.VertexTerm V K where
  side := t.side
  coeff := 1
  onCut x := b.repr (t.left x) j
  offCut y := t.read (b j * t.right y)

omit [Fintype J] in
theorem scalarTerm_side (t : LocalReadout (V:=V) (K:=K) (A:=A))
    (b : Basis J K A) (j : J) : (t.scalarTerm b j).side = t.side := rfl

theorem scalarizes (t : LocalReadout (V:=V) (K:=K) (A:=A))
    (b : Basis J K A) (σ : V → Bool) :
    t.value σ = ∑ j, (t.scalarTerm b j).value σ := by
  simpa only [value, scalarTerm, SeparatedRank.VertexTerm.value, one_mul] using
    readout_mul b t.read (t.left (SeparatedRank.CutTerm.restrict t.side σ))
      (t.right (SeparatedRank.CutTerm.restrict t.sideᶜ σ))

end LocalReadout

section Groups

variable {I D : Type*} [Fintype D] [DecidableEq D] {L : V → I → D}

/-- Regroup actual local factors before applying a joint linear readout. -/
def fromGroup (t : GroupProducts.GroupTerm L A) (symbols : I → Finset D)
    (read : A →ₗ[K] K) : LocalReadout (V:=V) (K:=K) (A:=A) where
  side := (t.toVertexTerm symbols).side
  left x := t.coeff * (t.toVertexTerm symbols).onCut x
  right := (t.toVertexTerm symbols).offCut
  read := read

theorem fromGroup_value (t : GroupProducts.GroupTerm L A) (symbols : I → Finset D)
    (read : A →ₗ[K] K) (σ : V → Bool) :
    (fromGroup t symbols read).value σ = read (t.value σ) := by
  change read ((t.coeff *
    BalancedUnion.localProduct (fun v => L v t.coordinate) t.factor (symbols t.coordinate)
      (fun v => σ v.1)) *
    BalancedUnion.localProduct (fun v => L v t.coordinate) t.factor ((symbols t.coordinate)ᶜ)
      (fun v => σ v.1)) = read (t.coeff * ∏ a, t.factor a (fun v => σ v.1))
  rw [mul_assoc, ← BalancedUnion.group_product_separates (fun v => L v t.coordinate)
    t.factor (symbols t.coordinate) σ]

end Groups

variable {T ι : Type*} [Fintype T] [Fintype ι] [DecidableEq ι]

/-- The full-rank final output forces dimension times distinct-register count.
The readout is allowed to differ for every register, and all coefficients may
have signs; no coefficient-by-coefficient materialization is assumed. -/
theorem readout_vertex_barrier (b : Basis J K A)
    (terms : T → LocalReadout (V:=V) (K:=K) (A:=A))
    (F : (V → Bool) → K) (hF : ∀ σ, F σ = ∑ t, (terms t).value σ)
    (e : (ι × Bool) ↪ V)
    (hfull : (Matrix.of fun x y => F (SeparatedRank.pinnedSigns e x y)).rank =
      2 ^ Fintype.card ι)
    (d : ℕ) (hgap : ∀ t, d ≤ SeparatedRank.endpointImbalance e (terms t).side) :
    2 ^ d ≤ Fintype.card T * Fintype.card J := by
  let scalar : T × J → SeparatedRank.VertexTerm V K := fun tj =>
    (terms tj.1).scalarTerm b tj.2
  have hv : ∀ σ, F σ = ∑ tj, (scalar tj).value σ := by
    intro σ
    rw [hF, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun t _ => (terms t).scalarizes b σ
  simpa only [Fintype.card_prod] using
    SeparatedRank.vertex_barrier scalar F hv e hfull d (fun tj => hgap tj.1)

section Main

variable {I P S R D : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype P] [Fintype D] [DecidableEq D] [Nonempty D] [Nonempty V]
  [CommRing R] [CommRing S] [Nontrivial S]
  {E : Finset (V × V)} {pin : V ↪ P} {cell : P → (I → D) × (I → D)} {cap : ℕ}

/-- Concrete rational/main final-output corollary using the incidence-derived
cuts, allowing a joint linear readout from each completed algebra register. -/
theorem main_readout_barrier (G : MainIncidence.Layout E pin cell cap)
    (hsize : 7776 * (Fintype.card I : ℚ) * (4 * cap * (Fintype.card I : ℚ)) /
      (FiniteGrowth.coefficient G.gamma (1/4)) ^ 2 < Fintype.card V)
    (b : Basis J K A)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → LocalReadout (V:=V) (K:=K) (A:=A)) (assigned : T → I)
    (hside : ∀ t, (terms t).side = EmpiricalCutMoments.labelCut
      (MainIncidence.labels pin cell) id G.symbols (assigned t))
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4) * Fintype.card V) ^ 2 ≤
      16 * (cap : ℚ) * (Fintype.card I : ℚ) * (d : ℚ)^2 ∧
      2^d ≤ Fintype.card T * Fintype.card J := by
  let scalar : T × J → SeparatedRank.VertexTerm V K := fun tj =>
    (terms tj.1).scalarTerm b tj.2
  have hv : ∀ σ, embed (output σ) = ∑ tj, (scalar tj).value σ := by
    intro σ
    rw [hrepresentation, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun t _ => (terms t).scalarizes b σ
  obtain ⟨d, hd, hc⟩ := MainIncidence.main_modular_cut_barrier G hsize embed residue
    hinjective output scalar (fun tj => assigned tj.1) (fun tj => hside tj.1) hv hcorrect
  exact ⟨d, hd, by simpa only [Fintype.card_prod] using hc⟩

/-- Direct incidence theorem for full group products in any commutative finite
algebra. Coefficient rings with one or two truncations use their ordinary
monomial bases; no evaluation homomorphism out of a quotient is assumed. -/
theorem main_group_readout_barrier (G : MainIncidence.Layout E pin cell cap)
    (hsize : 7776 * (Fintype.card I : ℚ) * (4 * cap * (Fintype.card I : ℚ)) /
      (FiniteGrowth.coefficient G.gamma (1/4)) ^ 2 < Fintype.card V)
    (b : Basis J K A)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → GroupProducts.GroupTerm (MainIncidence.labels pin cell) A)
    (read : T → A →ₗ[K] K)
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, read t ((terms t).value σ))
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4) * Fintype.card V) ^ 2 ≤
      16 * (cap : ℚ) * (Fintype.card I : ℚ) * (d : ℚ)^2 ∧
      2^d ≤ Fintype.card T * Fintype.card J := by
  apply main_readout_barrier G hsize b embed residue hinjective output
    (fun t => fromGroup (terms t) G.symbols (read t)) (fun t => (terms t).coordinate)
    (fun _ => rfl) _ hcorrect
  intro σ
  simpa only [fromGroup_value] using hrepresentation σ

end Main

#print axioms readout_mul
#print axioms LocalReadout.scalarizes
#print axioms fromGroup_value
#print axioms readout_vertex_barrier
#print axioms main_readout_barrier
#print axioms main_group_readout_barrier

end FiniteAlgebraReadout
