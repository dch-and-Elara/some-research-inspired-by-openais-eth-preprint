import J6IntegralDeformation
import J6DeformationReadout
import J6R9RecursiveRun
import J6R9PacketRealTile

/-! The actual Appendix D global and local contractions, over
Q[U]/f[V]/(V^ell) and Z_(2)[U]/f[V]/(V^ell), respectively.
Only the Cauchy entries, not the vertex weights, originate over the
scalar odd localization. Polynomial transport treats the original
entrywise lifts as fixed integral coefficients at every retained node. -/
namespace J6R10Integral

open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid J6R9Recursive
open J6ActiveUniqueness J6ActivePrintedHermite

/-- Same ordered edge coordinates are used on the two sides of the
deformed contraction. The physical atlas assigns a packet and an
in-range slot to every actual real edge, omitting all unused slots. -/
structure Atlas (P K : Type*) (a : ℕ) where
  page : P → K
  slot : P → Fin (2^a)
  injective : Function.Injective (fun i => (page i, slot i))

variable {P K : Type*} [Fintype P] [DecidableEq K] {a : ℕ}

def Atlas.index (W : Atlas P K a) (i : P) : ℤ := ((W.slot i).val : ℤ)

omit [Fintype P] [DecidableEq K] in
theorem Atlas.in_grid (W : Atlas P K a) (i j : P) :
    W.index j - W.index i ∈ grid a :=
  J6R9PacketRealTile.difference_mem_grid (W.slot i) (W.slot j)

omit [Fintype P] [DecidableEq K] in
theorem Atlas.index_injective (W : Atlas P K a) :
    Function.Injective (fun i => (W.page i, W.index i)) := by
  intro i j h
  apply W.injective
  refine Prod.ext (congrArg (Prod.fst : K × ℤ → K) h) (Fin.ext ?_)
  change (W.slot i).val = (W.slot j).val
  have hs : (↑(W.slot i).val : ℤ) = ↑(W.slot j).val := congrArg (Prod.snd : K × ℤ → ℤ) h
  exact_mod_cast hs

section Contract
variable {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]

/-- Literal multilinear extension with double Boolean sum; the
coefficient ring is not required to be a domain. -/
noncomputable def contract (M : P → P → A) (U V : (P → Bool) → A) : A :=
  ∑ Y : P → Bool, ∑ Xb : P → Bool, (U Y * V Xb) *
    ∏ i, let z := ∑ j, if Xb j then M i j else 0
         if Y i then z else 1-z

omit [DecidableEq K] in
theorem map_contract (g : A →+* B) (M : P → P → A) (U V : (P → Bool) → A) :
    g (contract M U V) = contract (fun i j => g (M i j)) (g ∘ U) (g ∘ V) := by
  classical
  simp only [contract,map_sum,map_mul,map_prod, Function.comp_apply]
  refine Finset.sum_congr rfl (fun Y _ => Finset.sum_congr rfl (fun Xb _ => ?_))
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hr : (∑ j, g (if Xb j then M i j else 0)) =
      ∑ j, if Xb j then g (M i j) else 0 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    cases Xb j <;> simp
  cases Y i <;> simp [map_sum,hr]

theorem network_eq_contract [Algebra ℚ R] (page : P → K) (slot : P → ℤ)
    (a : ℕ) (A B : (P → Bool) → R) :
    J6DeformationPoly.network page slot a A B =
      contract (J6DeformationPoly.matrix page slot a) (C ∘ A) (C ∘ B) := by
  simp only [J6DeformationPoly.network,contract,Function.comp_apply,map_mul]
end Contract

section Entries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem global_entry_map (a : ℕ) (k : ℤ) :
    (J6DeformationPoly.entry ℚ a k).map (algebraMap ℚ R) = J6DeformationPoly.entry R a k := by
  unfold J6DeformationPoly.entry
  rw [Polynomial.map_mul,Polynomial.map_C,Algebra.algebraMap_self,RingHom.id_apply,
    Polynomial.map_prod]
  congr 1
  refine Finset.prod_congr rfl (fun q _ => ?_)
  rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,map_intCast]

theorem coordinate_map (a : ℕ) (t : ℤ) :
    (J6DeformationLocal.coordinate a t).map (algebraMap ℚ R) =
      coord (dyadicUnit (R:=R) a) (t:R) := by
  have hp : (dyadicUnit (R:=R) a : R) = algebraMap ℚ R ((2:ℚ)^(a+1)) := rfl
  unfold J6DeformationLocal.coordinate coord
  rw [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C,
    Polynomial.map_C,hp,map_intCast,add_comm]

end Entries

variable (f : ℤ[X]) (ell : ℕ)

noncomputable def integralEntry (W : Atlas P K a) (t : ℤ) (i j : P) :
    (IntRing f ell)[X] :=
  (J6IntegralDeformation.localEntry W.page W.index a t i j).map (localScalar f ell)

noncomputable def globalNetwork (W : Atlas P K a) (U V : (P → Bool) → IntRing f ell) :
    (RatRing f ell)[X] :=
  J6DeformationPoly.network W.page W.index a (embed f ell ∘ U) (embed f ell ∘ V)

noncomputable def integralNetwork (W : Atlas P K a) (t : ℤ)
    (U V : (P → Bool) → IntRing f ell) : (IntRing f ell)[X] :=
  contract (integralEntry f ell W t) (C ∘ U) (C ∘ V)

omit [Fintype P] in
theorem entry_embed (W : Atlas P K a) {t : ℤ} (ht : t ∈ grid a) (i j : P) :
    (integralEntry f ell W t i j).map (embed f ell) =
      atNode (dyadicUnit a) (t:RatRing f ell)
        (J6DeformationPoly.matrix W.page W.index a i j) := by
  let g := algebraMap ℚ (RatRing f ell)
  have hg : (embed f ell).comp (localScalar f ell) = g.comp twoLocalRat :=
    RingHom.ext (embed_localScalar f ell)
  unfold integralEntry J6IntegralDeformation.localEntry J6DeformationPoly.matrix
  by_cases h : W.page i = W.page j
  · rw [if_pos h,if_pos h,Polynomial.map_map,hg,← Polynomial.map_map,
      ← J6DeformationLocal.entry_local_map ht (W.in_grid i j),
      Polynomial.map_comp,global_entry_map,coordinate_map,atNode_apply]
  · rw [if_neg h,if_neg h,Polynomial.map_zero,Polynomial.map_zero,map_zero]

theorem network_embed (W : Atlas P K a) {t : ℤ} (ht : t ∈ grid a)
    (U V : (P → Bool) → IntRing f ell) :
    (integralNetwork f ell W t U V).map (embed f ell) =
      atNode (dyadicUnit a) (t:RatRing f ell) (globalNetwork f ell W U V) := by
  unfold integralNetwork globalNetwork
  rw [network_eq_contract]
  change Polynomial.mapRingHom (embed f ell) (contract _ _ _) = atNode _ _ (contract _ _ _)
  rw [map_contract,map_contract]
  have hc (x : IntRing f ell) : atNode (dyadicUnit a) (t:RatRing f ell) (C (embed f ell x)) =
      Polynomial.mapRingHom (embed f ell) (C x) := by
    rw [atNode_apply,C_comp,coe_mapRingHom,map_C]
  simp only [Function.comp_def,hc]
  congr 1
  exact funext (fun i => funext (entry_embed f ell W ht i))

theorem network_degree (W : Atlas P K a) (U V : (P → Bool) → IntRing f ell) :
    (globalNetwork f ell W U V).natDegree ≤ J9PrintedSchedule.degreeBound (Fintype.card P) (2^a) :=
  J6DeformationPoly.network_degree W.page W.index a _ _ (fun i j _ => W.in_grid i j)

theorem network_origin (W : Atlas P K a) (U V : (P → Bool) → IntRing f ell) :
    (globalNetwork f ell W U V).eval 0 = embed f ell (∑ y, U y * V y) := by
  rw [globalNetwork,J6DeformationReadout.exact_origin W.page W.index a _ _ W.index_injective,map_sum]
  simp only [Function.comp_apply,map_mul]

theorem local_degree (hf : f.Monic) (W : Atlas P K a) {t : ℤ} (ht : t ∈ grid a)
    (U V : (P → Bool) → IntRing f ell) :
    (integralNetwork f ell W t U V).natDegree ≤ J9PrintedSchedule.degreeBound (Fintype.card P) (2^a) := by
  rw [← natDegree_map_eq_of_injective (embed_inj f hf ell),network_embed f ell W ht]
  exact (atNode_degree _ _ _).trans (network_degree f ell W U V)

#print axioms Atlas.in_grid
#print axioms Atlas.index_injective
#print axioms map_contract
#print axioms entry_embed
#print axioms network_embed
#print axioms network_degree
#print axioms network_origin
#print axioms local_degree
end J6R10Integral
