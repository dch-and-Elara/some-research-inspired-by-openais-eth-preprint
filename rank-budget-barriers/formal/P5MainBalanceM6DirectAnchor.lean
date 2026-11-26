import P5MainBalanceM6DirectRecipe
import Mathlib.Data.ZMod.Basic

/-! Exact counts for the actual printed unary, edge, and cycle factors.
No output, parity, or global CNF-equivalence premise is supplied. -/
namespace P5MainBalance.M6.Direct
open P5MainBalance P5MainBalance.M6 P5MainIterator Polynomial
open scoped BigOperators Classical

variable {V Copy I B : Type*} [Fintype V] [DecidableEq V] [Fintype Copy]
  [Fintype I] [Fintype B] [LinearOrder B]
variable {graph : Finset (V×V)} {left right : graph→Fin 4}

def locallySat (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right) :
    (f : Factor graph)→({v : V // signedOwner L.physical (MainClonedCNF.pinPort graph) v=f}→Bool)→
      ((V×Fin 4)→Bool)→Prop
  | .inl v, s, x => x (v,0)=pinSign L v s
  | .inr (.inl e), _, x => x (e.val.1,left e)=true ∨ x (e.val.2,right e)=true
  | .inr (.inr (v,i)), _, x => x (v,i)=false ∨ x (v,i+1)=true

set_option maxHeartbeats 13000000 in
omit [Fintype V] [DecidableEq V] [Fintype Copy] [Fintype I] [Fintype B] in
theorem local_anchor_exact (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right)
    (f : Factor graph)
    (s : {v : V // signedOwner L.physical (MainClonedCNF.pinPort graph) v=f}→Bool)
    (x : V×Fin 4→Bool) :
    atAnchorFactor L.physical (MainClonedCNF.pinPort graph) (recipe L) f s x =
      if locallySat L f s x then 1 else 0 := by
  let A (e : MainClonedCNF.Port graph) : Bivariate :=
    C (C (qbits x (L.physical.placement.owner e)))
  have hC (p : ℚ[X]) : Polynomial.constantCoeff (C p:Bivariate)=p := coeff_C_zero
  have link :
      Polynomial.constantCoeff ((recipe L).factorScore f s A) =
        atAnchorFactor L.physical (MainClonedCNF.pinPort graph) (recipe L) f s x := by
    unfold Recipe.factorScore atAnchorFactor A
    simp only [map_sum,map_mul,map_prod,hC]
  rw [←link,factorScore_literal]
  rcases f with v|u|⟨v,i⟩
  · cases hp : pinSign L v s <;> cases hx : x (v,0) <;>
      simp [actualClauseFactor,locallySat,hp,hx,A,pin,L.owner_is,ownerOf,
        qbits,BooleanMeasurement.bit]
  · cases hx : x (u.val.1,left u) <;> cases hy : x (u.val.2,right u) <;>
      simp [actualClauseFactor,locallySat,hx,hy,A,edge,L.owner_is,ownerOf,
        qbits,BooleanMeasurement.bit]
  · cases hx : x (v,i) <;> cases hy : x (v,i+1) <;>
      simp [actualClauseFactor,locallySat,hx,hy,A,cycle,L.owner_is,ownerOf,
        qbits,BooleanMeasurement.bit]

set_option maxHeartbeats 13000000 in
omit [DecidableEq V] [Fintype Copy] [Fintype I] [Fintype B] in
theorem all_local_sat_is_cloned_formula (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right)
    (x : V×Fin 4→Bool) (σ : V→Bool) :
    (∀ f,locallySat L f (fun v=>σ v.val) x) ↔
      Std.Sat.CNF.Sat x (MainClonedCNF.formula graph left right σ) := by
  rw [MainClonedCNF.sat_iff]
  constructor
  · intro h
    have hcycle (v : V) : Std.Sat.CNF.Sat x (MainClonedCNF.cycle v) := by
      have h₀ := h (.inr (.inr (v,0)))
      have h₁ := h (.inr (.inr (v,1)))
      have h₂ := h (.inr (.inr (v,2)))
      have h₃ := h (.inr (.inr (v,3)))
      simpa [locallySat,MainClonedCNF.cycle,Std.Sat.CNF.sat_def] using And.intro h₀ (And.intro h₁ (And.intro h₂ h₃))
    have he (v : V) : x (v,0)=σ v := h (.inl v)
    have hEq : x = fun u=>σ u.1 := by
      funext u
      exact ((MainClonedCNF.cycle_sat u.1 x).mp (hcycle u.1) u.2).trans (he u.1)
    refine ⟨hEq,?_⟩
    intro e hm
    have htest := h (.inr (.inl ⟨e,hm⟩))
    simpa [locallySat,hEq] using htest
  · rintro ⟨hc,hg⟩ f
    subst x
    rcases f with v|e|⟨v,i⟩
    · rfl
    · exact hg e.val e.property
    · change σ v=false ∨ σ v=true
      cases σ v <;> simp

theorem direct_anchor_count_is_pinned (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right)
    (t : I→ℚ) (M : Mix Copy I B) (σ : V→Bool) :
    retainedOrigin 1 (actualH L.physical (MainClonedCNF.pinPort graph) t M (recipe L) σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula graph σ):ℚ) := by
  rw [direct_anchor_count_from_literal_factors L.physical (MainClonedCNF.pinPort graph) t M
    (recipe L) (locallySat L) (local_anchor_exact L)]
  rw [←MainClonedCNF.modelCount_cloned graph left right σ]
  congr 1
  unfold nativeModelCount PinnedCNF.modelCount
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact (all_local_sat_is_cloned_formula L x σ).trans (Std.Sat.CNF.sat_def _ _)

theorem direct_terminal_witness (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right)
    (t : I→ℚ) (M : Mix Copy I B) :
    ∃ out : (V→Bool)→ℤ,
      (∀ σ,(out σ:ℚ)=retainedOrigin 1 (actualH L.physical (MainClonedCNF.pinPort graph) t M (recipe L) σ)) ∧
      (∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula graph σ):ZMod 2)) := by
  refine ⟨fun σ => (PinnedCNF.modelCount (PinnedCNF.formula graph σ):ℤ),?_,?_⟩
  · intro σ
    rw [direct_anchor_count_is_pinned L t M,Int.cast_natCast]
  · intro σ
    rw [Int.cast_natCast]

#print axioms local_anchor_exact
#print axioms all_local_sat_is_cloned_formula
#print axioms direct_anchor_count_is_pinned
#print axioms direct_terminal_witness
end P5MainBalance.M6.Direct
