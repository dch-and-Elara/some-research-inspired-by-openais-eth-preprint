import P5A2Powers
import HybridFrontier
import FiniteAlgebraReadout

/-! Exact generic readout capacity, original v7 lines 552–577.
The factors are actual linear forms on the given finite algebra.
The Hankel and double-quotient specializations are separate P5A2 theorems. -/
namespace Paper5.GenericReadout
open Matrix Module
open scoped BigOperators Classical

variable {K A J : Type*} [Field K] [CommRing A] [Algebra K A] [Fintype J]

noncomputable def multiplicationPair (read : A→ₗ[K]K) : A→ₗ[K](A→ₗ[K]K) where
  toFun u := read.comp (Algebra.lmul K A u)
  map_add' u v := by
    ext w
    change read ((u+v)*w)=read (u*w)+read (v*w)
    rw [add_mul,map_add]
  map_smul' r u := by
    ext w
    change read ((r • u)*w)=r • read (u*w)
    rw [smul_mul_assoc,map_smul]

omit [Fintype J] in
theorem multiplicationPair_apply (read : A→ₗ[K]K) (u v : A) :
    multiplicationPair read u v=read (u*v) := rfl

omit [Fintype J] in
def Realizes (read : A→ₗ[K]K) (r : ℕ) : Prop :=
  ∃ (f g : Fin r→A→ₗ[K]K),∀u v,read (u*v)=∑ j,f j u*g j v

omit [Fintype J] in
theorem extends_basis_identity (b : Basis J K A) (read : A→ₗ[K]K)
    {r : ℕ} (f g : Fin r→A→ₗ[K]K)
    (h : ∀ i j,read (b i*b j)=∑ p,f p (b i)*g p (b j)) :
    ∀u v,read (u*v)=∑ p,f p u*g p v := by
  have he : multiplicationPair read=∑ p,(f p).smulRight (g p) := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    simpa only [multiplicationPair_apply,LinearMap.sum_apply,LinearMap.smulRight_apply,
      LinearMap.smul_apply,smul_eq_mul] using h i j
  intro u v
  have hx := congrArg (fun h' : A→ₗ[K](A→ₗ[K]K)=>h' u v) he
  simpa only [multiplicationPair_apply,LinearMap.sum_apply,LinearMap.smulRight_apply,
    LinearMap.smul_apply,smul_eq_mul] using hx

noncomputable def coordinateForm (b : Basis J K A) (w : J→K) : A→ₗ[K]K :=
  ∑ i,w i • b.coord i

theorem coordinateForm_on_basis (b : Basis J K A) (w : J→K) (i : J) :
    coordinateForm b w (b i)=w i := by
  unfold coordinateForm
  rw [LinearMap.sum_apply,Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp only [LinearMap.smul_apply,P5A2.coord_basis,if_neg (Ne.symm hj),smul_zero]
  · simp

noncomputable def capacity (b : Basis J K A) (read : A→ₗ[K]K) : ℕ :=
  (P5A2.pairing b read).rank

theorem rank_le_realization (b : Basis J K A) (read : A→ₗ[K]K) (r : ℕ)
    (h : Realizes read r) : capacity b read≤r := by
  obtain ⟨f,g,hfg⟩ := h
  let U : Matrix J (Fin r) K := Matrix.of fun i s=>f s (b i)
  let V : Matrix (Fin r) J K := Matrix.of fun s j=>g s (b j)
  have he : P5A2.pairing b read=U*V := Matrix.ext (fun i j=>hfg (b i) (b j))
  rw [capacity,he]
  exact (Matrix.rank_mul_le_left U V).trans (by simpa only [Fintype.card_fin] using U.rank_le_card_width)

theorem realizes_at_rank (b : Basis J K A) (read : A→ₗ[K]K) :
    Realizes read (capacity b read) := by
  obtain ⟨U,V,h⟩ := HybridFrontier.exact_factorization (P5A2.pairing b read)
  refine ⟨fun s=>coordinateForm b (fun i=>U i s),
    fun s=>coordinateForm b (fun j=>V s j),?_⟩
  apply extends_basis_identity b read
  intro i j
  simp only [coordinateForm_on_basis]
  exact congrArg (fun M : Matrix J J K=>M i j) h

theorem exact_readout_capacity (b : Basis J K A) (read : A→ₗ[K]K) :
    Realizes read (capacity b read) ∧
      (∀r,Realizes read r→capacity b read≤r) ∧ capacity b read≤Module.finrank K A := by
  refine ⟨realizes_at_rank b read,rank_le_realization b read,?_⟩
  rw [Module.finrank_eq_card_basis b]
  exact (P5A2.pairing b read).rank_le_card_width

theorem capacity_basis_independent {I : Type*} [Fintype I] (b : Basis J K A)
    (b' : Basis I K A) (read : A→ₗ[K]K) : capacity b read=capacity b' read :=
  le_antisymm (rank_le_realization b read _ (realizes_at_rank b' read))
    (rank_le_realization b' read _ (realizes_at_rank b read))

theorem capacity_of_zero (b : Basis J K A) : capacity b (0 : A→ₗ[K]K)=0 := by
  apply Nat.le_zero.mp
  apply rank_le_realization
  refine ⟨fun _=>0,fun _=>0,?_⟩
  intro u v
  simp

#print axioms multiplicationPair_apply
#print axioms extends_basis_identity
#print axioms rank_le_realization
#print axioms realizes_at_rank
#print axioms exact_readout_capacity
#print axioms capacity_basis_independent
#print axioms capacity_of_zero
end Paper5.GenericReadout
