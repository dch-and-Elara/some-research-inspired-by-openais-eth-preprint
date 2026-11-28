import V8NativeMessageN6MainUntied

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

/-! The optional N3/N6 prefix uses the actual quotient reduction of
one completed jet, with the same original address and private lists. -/
namespace V8NativeMessage.N6
open scoped Classical BigOperators Polynomial
open Paper5.HybridClosure V8CapacityUnified.U7 Polynomial
open V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

def prefixJet {k J : ℕ} (h : k≤J) : Jet J →ₐ[ℚ] Jet k :=
  AdjoinRoot.algHomOfDvd (X^J) (X^k) (pow_dvd_pow _ h)

theorem prefixJet_mk {k J : ℕ} (h : k≤J) (f : ℚ[X]) :
    prefixJet h (AdjoinRoot.mk (X^J) f)=AdjoinRoot.mk (X^k) f := by
  rw [prefixJet,AdjoinRoot.algHomOfDvd,AdjoinRoot.liftHom_mk,AdjoinRoot.aeval_eq]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {F : Finset (TriVertex V×TriVertex V)} {r Q J k : ℕ}
variable (L : CloneTuple F r Q J) (cubic : ∀ v, GraphCutMoments.degree F v=3)
  (h : feasible L.frame) (P : FixedLists L)

theorem N6_prefix_group (fits : k≤J) (read : Jet k →ₗ[ℚ] ℚ)
    (correct : ∀ σ, read (prefixJet fits (completed L cubic h P σ))=UM σ)
    (g : Fin r) :
    2^(wholeTriangles (pinGroup L) g).card≤k*P.count g := by
  let n := (wholeTriangles (pinGroup L) g).card
  let s := groupSlice (pinGroup L) g
  let rd := absorb read (prefixJet fits (otherJet L cubic h P g))
  let a (j : Fin (P.count g)) (x : Fin n→Bool) :=
    prefixJet fits (leftPoint L cubic h P g j (leftCut s) (word s x (fun _ => true)))
  let b (j : Fin (P.count g)) (y : Fin n→Bool) :=
    prefixJet fits (rightPoint L cubic h P g j (leftCut s) (word s (fun _ => true) y))
  let M : Matrix (Fin n→Bool) (Fin n→Bool) ℚ :=
    ∑ j : Fin (P.count g), C3.mixedTerm rd (a j) (b j) (fun _ => 1) (fun _ => 1)
  have fact : M = matchingTarget ℚ n := by
    ext x y
    have hs := splice_slice s (leftCut s) x y (leftCut_left s) (leftCut_right s)
    have hL : ∀ i, pinGroup L (leftPin s i)=g := fun i => groupSlice_seated (pinGroup L) g i (s.left i)
    have hR : ∀ i, pinGroup L (rightPin s i)=g := fun i => groupSlice_seated (pinGroup L) g i (s.right i)
    calc
      M x y = ∑ j : Fin (P.count g), rd (a j x*b j y) := by
        simp [M,Matrix.sum_apply,C3.mixedTerm]
      _ = ∑ j : Fin (P.count g), rd (prefixJet fits (entry L cubic h P g j (word s x y))) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [a,b]
        rw [← map_mul,← hs,point_factors L cubic h P]
      _ = rd (prefixJet fits (groupJet L cubic h P g (word s x y))) := by
        rw [groupJet,map_sum,map_sum]
      _ = read (prefixJet fits (completed L cubic h P (word s x y))) := by
        rw [completed_one_active_group s L cubic h P g hL hR,map_mul]
        rfl
      _ = _ := (correct _).trans (UM_on_slice s x y)
  change 2^n≤_
  rw [← matching_full_rank n, ← fact]
  exact finite_private_rank rd a b

theorem N6_prefix_untied (fits : k≤J) (read : Jet k→ₗ[ℚ]ℚ)
    (correct : ∀ σ, read (prefixJet fits (completed L cubic h P σ))=UM σ) :
    2^(((splitTriangles (pinGroup L)).card+1)/2)≤k := by
  obtain ⟨χ,m,s,hm,hl,hr⟩ := split_has_slice (pinGroup L)
  let a (x : Fin m→Bool) := prefixJet fits (colorJet L cubic h P χ true (word s x (fun _=>true)))
  let b (y : Fin m→Bool) := prefixJet fits (colorJet L cubic h P χ false (word s (fun _=>true) y))
  have fact : C3.mixedTerm read a b (fun _=>1) (fun _=>1) = matchingTarget ℚ m := by
    ext x y
    simp only [C3.mixedTerm,Matrix.of_apply,mul_one]
    dsimp only [a,b]
    rw [← map_mul,← completed_by_colored_groups L cubic h P s χ hl hr x y]
    exact (correct _).trans (UM_on_slice s x y)
  have cap := read_rank read a b
  rw [fact,matching_full_rank] at cap
  exact (Nat.pow_le_pow_right (by decide) (show ((splitTriangles (pinGroup L)).card+1)/2≤m by omega)).trans cap

#print axioms prefixJet_mk
#print axioms N6_prefix_group
#print axioms N6_prefix_untied

end
end V8NativeMessage.N6
