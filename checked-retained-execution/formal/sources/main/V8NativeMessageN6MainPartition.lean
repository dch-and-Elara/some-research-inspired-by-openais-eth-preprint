import V8NativeMessageN6MainUntied
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000

/-! Quantitative finite form of the printed N6 consequences. All
vertex counts refer to the actual graph's triangles, with three
distinct external unary signs per triangle. -/
namespace V8NativeMessage.N6
open scoped Classical BigOperators Polynomial
open Paper5.HybridClosure V8CapacityUnified.U7
open V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {V G : Type*} [Fintype V] [Fintype G] [DecidableEq G]

theorem whole_split_partition (owner : TriVertex V→G) :
    (∑ g, (wholeTriangles owner g).card)+(splitTriangles owner).card = Fintype.card V := by
  have hg (g : G) : (wholeTriangles owner g).card =
      ∑ v : V, (if ∀ j : Fin 3, owner (v,j)=g then 1 else 0) := by
    unfold wholeTriangles
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  have hs : (splitTriangles owner).card =
      ∑ v : V, (if ∃ a b : Fin 3, owner (v,a)≠owner (v,b) then 1 else 0) := by
    unfold splitTriangles
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [hg,hs]
  rw [Finset.sum_comm,← Finset.sum_add_distrib,← Finset.card_univ,Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro v _
  by_cases sp : ∃ a b : Fin 3, owner (v,a)≠owner (v,b)
  · obtain ⟨a,b,h⟩ := sp
    have hg' (g : G) : ¬∀ j : Fin 3, owner (v,j)=g := fun h' => h ((h' a).trans (h' b).symm)
    simp [hg',show ∃ a b : Fin 3, owner (v,a)≠owner (v,b) from ⟨a,b,h⟩]
  · have h₀ (j : Fin 3) : owner (v,j)=owner (v,0) := by
      by_contra hn
      exact sp ⟨j,0,hn⟩
    have hg' (g : G) : (∀ j : Fin 3,owner (v,j)=g) ↔ g=owner (v,0) :=
      ⟨fun h => (h 0).symm,fun h j => (h₀ j).trans h.symm⟩
    simp [hg',sp]

theorem some_many_whole [Nonempty G] (owner : TriVertex V→G) :
    ∃ g, Fintype.card V ≤ Fintype.card G*(wholeTriangles owner g).card+(splitTriangles owner).card := by
  obtain ⟨g,_,gmax⟩ := Finset.exists_max_image (Finset.univ : Finset G)
    (fun j => (wholeTriangles owner j).card) Finset.univ_nonempty
  refine ⟨g,?_⟩
  rw [← whole_split_partition owner]
  apply Nat.add_le_add_right
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    (Finset.sum_le_sum (fun j hj => gmax j hj) :
      (∑ j : G, (wholeTriangles owner j).card) ≤ ∑ _j : G, (wholeTriangles owner g).card)

omit [Fintype G] in
theorem when_tied_no_split (owner : TriVertex V→G)
    (tied : ∀ v (j : Fin 3), owner (v,j)=owner (v,0)) :
    (splitTriangles owner).card=0 := by
  change (Finset.univ.filter (fun v : V => ∃ a b : Fin 3, owner (v,a)≠owner (v,b))).card=0
  have h (v : V) : ¬∃ a b : Fin 3, owner (v,a)≠owner (v,b) := by
    rintro ⟨a,b,ne⟩
    exact ne ((tied v a).trans (tied v b).symm)
  simp [h]

section Literal
variable [DecidableEq V]
variable {F : Finset (TriVertex V×TriVertex V)} {r Q J : ℕ}
variable (L : CloneTuple F r Q J) (cubic : ∀ v, GraphCutMoments.degree F v=3)
  (h : feasible L.frame) (P : FixedLists L)

theorem N6_untied_log (read : Jet J→ₗ[ℚ]ℚ)
    (correct : ∀ σ, read (completed L cubic h P σ)=UM σ) :
    (splitTriangles (pinGroup L)).card ≤ 2*Nat.log 2 J := by
  have hp := N6_untied L cubic h P read correct
  have hb := Nat.le_log_of_pow_le (by decide : 1<2) hp
  omega

theorem N6_largest_whole (read : Jet J→ₗ[ℚ]ℚ) (hr : 0<r)
    (correct : ∀ σ, read (completed L cubic h P σ)=UM σ) :
    ∃ g : Fin r, Fintype.card (TriVertex V) ≤
        3*(r*(wholeTriangles (pinGroup L) g).card+2*Nat.log 2 J) ∧
      2^(wholeTriangles (pinGroup L) g).card≤J*P.count g := by
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  obtain ⟨g,hg⟩ := some_many_whole (pinGroup L)
  refine ⟨g,?_,N6_group_list L cubic h P read correct g⟩
  rw [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm (Fintype.card V) 3]
  apply Nat.mul_le_mul_left
  simpa only [Fintype.card_fin] using hg.trans (Nat.add_le_add_left (N6_untied_log L cubic h P read correct) _)

theorem N6_largest_tied (read : Jet J→ₗ[ℚ]ℚ) (hr : 0<r)
    (tied : ∀ v (j : Fin 3), pinGroup L (v,j)=pinGroup L (v,0))
    (correct : ∀ σ, read (completed L cubic h P σ)=UM σ) :
    ∃ g : Fin r, Fintype.card (TriVertex V) ≤ 3*r*(wholeTriangles (pinGroup L) g).card ∧
      2^(wholeTriangles (pinGroup L) g).card≤J*P.count g := by
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  obtain ⟨g,hg⟩ := some_many_whole (pinGroup L)
  refine ⟨g,?_,N6_group_list L cubic h P read correct g⟩
  rw [when_tied_no_split (pinGroup L) tied,Fintype.card_fin,add_zero] at hg
  rw [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm (Fintype.card V) 3,Nat.mul_assoc]
  exact Nat.mul_le_mul_left 3 hg

end Literal

#print axioms whole_split_partition
#print axioms some_many_whole
#print axioms when_tied_no_split
#print axioms N6_untied_log
#print axioms N6_largest_whole
#print axioms N6_largest_tied

end
end V8NativeMessage.N6
