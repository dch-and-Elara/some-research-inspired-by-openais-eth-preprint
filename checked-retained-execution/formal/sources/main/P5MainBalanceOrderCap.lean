import P5MainBalanceCutBudget
import FiniteAlgebraReadout
import P5MainIteratorTrace
import P5A2Double

/-! A completed source coefficient register of order j uses the true
double truncation at V^ell and z^(j+1), and only its dimension is spent
on scalar cut rank. One does not scalarize every intermediate product. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Module

section Algebra
variable {V W T A J : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype T] [Fintype J] [CommRing A] [Algebra ℚ A]

theorem cut_length_of_readouts (S : Finset V) (b : Basis J ℚ A)
    (terms : T→FiniteAlgebraReadout.LocalReadout (V:=V) (K:=ℚ) (A:=A))
    (hside : ∀ t,(terms t).side=S) (f : (V→Bool)→ℚ)
    (hread : ∀ σ,f σ=∑ t,(terms t).value σ) :
    cutLength S f≤Fintype.card T * Fintype.card J := by
  let e := Fintype.equivFinOfCardEq (Fintype.card_prod T J)
  let p (i : T×J) := (terms i.1).scalarTerm b i.2
  apply cut_length_minimal
  refine ⟨fun i=>p (e.symm i),fun i=>hside (e.symm i).1,?_⟩
  intro σ
  rw [hread,e.symm.sum_comp (fun i : T×J => (p i).value σ),Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun t _ => (terms t).scalarizes b σ)

end Algebra

variable {V W I B Y : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype B] [DecidableEq B] [Fintype Y]

/-- The actual native local expression is indexed by the Taylor pairs
up to order j and feasible Y-fibers. The scalarization has exactly J⋅ell
channels, irrespective of the number of groups. -/
theorem native_order_rank_upper (L : V→I→B) (S : I→Finset B) (t : I) (j ell : ℕ)
    (hp : 0<ell)
    (terms : (P5MainIterator.TaylorList W j)×Y→GroupProducts.GroupTerm L (P5A2.Double ℚ ell (j+1)))
    (hnode : ∀ a,(terms a).coordinate=t)
    (read : (P5MainIterator.TaylorList W j)×Y→P5A2.Double ℚ ell (j+1)→ₗ[ℚ] ℚ)
    (K : (V→Bool)→ℚ)
    (hcoeff : ∀ σ,K σ=∑ a,read a ((terms a).value σ)) :
    cutLength (EmpiricalCutMoments.labelCut L id S t) K ≤
      (P5MainIterator.TaylorList W j).card * Fintype.card Y * (ell*(j+1)) := by
  let A := P5A2.Double ℚ ell (j+1)
  let b := P5A2.pairBasis (K:=ℚ) ell (j+1) hp
  have h := cut_length_of_readouts (EmpiricalCutMoments.labelCut L id S t) b
    (fun a => FiniteAlgebraReadout.fromGroup (terms a) S (read a))
    (fun a => by change EmpiricalCutMoments.labelCut L id S (terms a).coordinate=_;
                 rw [hnode a]) K (fun σ=>by simpa only [FiniteAlgebraReadout.fromGroup_value] using hcoeff σ)
  simpa only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] using h

#print axioms cut_length_of_readouts
#print axioms native_order_rank_upper
end P5MainBalance
