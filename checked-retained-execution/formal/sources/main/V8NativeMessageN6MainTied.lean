import V8NativeMessageN6MainLocal
import V8NativeMessageN6MainTriangles
import V8NativeMessageC3Rank
import P5HybridClosureGraph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5800000

/-! Original v8 N6 for the four-copy MAIN direct-clause register. The
assumption is equality to the specified internal triangle product on
the whole input cube, not parity and not a capacity promise. -/
namespace V8NativeMessage.N6
open scoped Classical BigOperators Polynomial
open Paper5.HybridClosure V8CapacityUnified.U7 Polynomial
open V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : ℕ} (S : TriangleSlice V m)

def leftCut (p : TriVertex V) : Bool := decide (p ∈ Set.range (leftPin S))

omit [Fintype V] in
theorem leftCut_left (i : Fin m) : leftCut S (leftPin S i)=true := by
  simp [leftCut]

omit [Fintype V] in
theorem leftCut_right (i : Fin m) : leftCut S (rightPin S i)=false := by
  have h : rightPin S i ∉ Set.range (leftPin S) := by
    rintro ⟨j,hj⟩
    have he : j=i := S.vertex.injective (congrArg Prod.fst hj)
    subst j
    exact S.distinct i (congrArg Prod.snd hj)
  simp [leftCut,h]

omit [Fintype V] in
theorem splice_slice (cut : TriVertex V→Bool) (x y : Fin m→Bool)
    (hl : ∀ i, cut (leftPin S i)=true) (hr : ∀ i, cut (rightPin S i)=false) :
    splice cut (word S x (fun _ => true)) (word S (fun _ => true) y) = word S x y := by
  funext v
  cases hcut : cut v with
  | false => simpa [splice,hcut] using (word_cross_right S x y cut hl v hcut).symm
  | true => simpa [splice,hcut] using (word_cross_left S x y cut hr v hcut).symm

variable {J : ℕ}

def absorb (ρ : Jet J →ₗ[ℚ] ℚ) (c : Jet J) : Jet J →ₗ[ℚ] ℚ where
  toFun z := ρ (z*c)
  map_add' a b := by simp [add_mul]
  map_smul' s z := by simp

theorem matching_full_rank (k : ℕ) : (matchingTarget ℚ k).rank=2^k := by
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (matching_det_ne_zero ℚ k)))]
  simp

def mainJetBasis (k : ℕ) : Module.Basis (Fin k) ℚ (Jet k) :=
  ((AdjoinRoot.powerBasis' (monic_X.pow k)).basis).reindex
    (finCongr (by simp [AdjoinRoot.powerBasis']))

theorem read_rank {X Y : Type*} [Fintype X] [Fintype Y]
    (ρ : Jet J →ₗ[ℚ] ℚ) (a : X→Jet J) (b : Y→Jet J) :
    (C3.mixedTerm ρ a b (fun _ => 1) (fun _ => 1)).rank ≤ J := by
  simpa only [Fintype.card_fin] using C3.mixedTerm_rank (mainJetBasis J) ρ a b
    (fun _ => 1) (fun _ => 1)

theorem finite_private_rank {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ}
    (ρ : Jet J →ₗ[ℚ] ℚ) (a : Fin n→X→Jet J) (b : Fin n→Y→Jet J) :
    (∑ k : Fin n, C3.mixedTerm ρ (a k) (b k) (fun _=>1) (fun _=>1)).rank ≤ J*n := by
  apply (V8CapacityUnified.U7.rank_sum_le Finset.univ _).trans
  calc
    _ ≤ ∑ _k : Fin n, J := Finset.sum_le_sum (fun k _ => read_rank ρ (a k) (b k))
    _ = _ := by simp [mul_comm]

section Literal
variable {F : Finset (TriVertex V×TriVertex V)} {r Q : ℕ}
variable (L : CloneTuple F r Q J) (cubic : ∀ v, GraphCutMoments.degree F v=3)
  (feasibleAt : feasible L.frame) (P : FixedLists L)

def otherJet (g : Fin r) : Jet J :=
  ∏ j ∈ Finset.univ.erase g, groupJet L cubic feasibleAt P j (fun _ => true)

/-- If an active slice is inside the indicated factor group, all other
complete group jets are fixed. Absorb their product in the one readout;
do not spend its rank parameter separately per group. -/
theorem completed_one_active_group (g : Fin r)
    (hL : ∀ i, pinGroup L (leftPin S i)=g) (hR : ∀ i, pinGroup L (rightPin S i)=g)
    (x y : Fin m→Bool) :
    completed L cubic feasibleAt P (word S x y) =
      groupJet L cubic feasibleAt P g (word S x y) * otherJet L cubic feasibleAt P g := by
  unfold completed otherJet
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => groupJet L cubic feasibleAt P j (word S x y)) (Finset.mem_univ g)]
  apply congrArg (groupJet L cubic feasibleAt P g (word S x y) * ·)
  apply Finset.prod_congr rfl
  intro j hj
  have hneq : j≠g := (Finset.mem_erase.mp hj).1
  apply groupJet_pin_local
  intro p hp
  apply word_off_pairs S x y p
  · intro i ep
    exact hneq (hp.symm.trans (ep ▸ hL i))
  · intro i ep
    exact hneq (hp.symm.trans (ep ▸ hR i))

theorem N6_group_list (read : Jet J →ₗ[ℚ] ℚ)
    (correct : ∀ σ, read (completed L cubic feasibleAt P σ)=UM σ)
    (g : Fin r) :
    2^(wholeTriangles (pinGroup L) g).card≤J*P.count g := by
  let n := (wholeTriangles (pinGroup L) g).card
  let s := groupSlice (pinGroup L) g
  let rd := absorb read (otherJet L cubic feasibleAt P g)
  let a (k : Fin (P.count g)) (x : Fin n→Bool) :=
    leftPoint L cubic feasibleAt P g k (leftCut s) (word s x (fun _ => true))
  let b (k : Fin (P.count g)) (y : Fin n→Bool) :=
    rightPoint L cubic feasibleAt P g k (leftCut s) (word s (fun _ => true) y)
  let M : Matrix (Fin n→Bool) (Fin n→Bool) ℚ :=
    ∑ k : Fin (P.count g), C3.mixedTerm rd (a k) (b k) (fun _ => 1) (fun _ => 1)
  have fact : M = matchingTarget ℚ n := by
    ext x y
    have hs := splice_slice s (leftCut s) x y (leftCut_left s) (leftCut_right s)
    have hL : ∀ i, pinGroup L (leftPin s i)=g := fun i => groupSlice_seated (pinGroup L) g i (s.left i)
    have hR : ∀ i, pinGroup L (rightPin s i)=g := fun i => groupSlice_seated (pinGroup L) g i (s.right i)
    calc
      M x y = ∑ k : Fin (P.count g), rd (a k x*b k y) := by
        simp [M,Matrix.sum_apply,C3.mixedTerm]
      _ = ∑ k : Fin (P.count g), rd (entry L cubic feasibleAt P g k (word s x y)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← hs,point_factors L cubic feasibleAt P]
      _ = rd (groupJet L cubic feasibleAt P g (word s x y)) := by
        rw [groupJet,map_sum]
      _ = read (completed L cubic feasibleAt P (word s x y)) := by
        rw [completed_one_active_group s L cubic feasibleAt P g hL hR]
        rfl
      _ = _ := (correct _).trans (UM_on_slice s x y)
  change 2^n≤_
  rw [← matching_full_rank n, ← fact]
  exact finite_private_rank rd a b

include feasibleAt in
/-- The source branch is the actual exhaustive restricted measurement
fibre, with the unrestricted private representatives of the first pass. -/
theorem N6_full_source_fibre (read : Jet J →ₗ[ℚ] ℚ)
    (correct : ∀ σ, read (nativeScan F cubic L σ).2.2=UM σ) (g : Fin r) :
    2^(wholeTriangles (pinGroup L) g).card≤J*Fintype.card (PrivateWord L g) := by
  apply N6_group_list L cubic feasibleAt (exhaustive L) read _ g
  intro σ
  rw [exhaustive_completed L cubic feasibleAt]
  exact correct σ

end Literal

/-- Authoritative four-clone family: internal triangles plus the actual
exterior perfect matching produced by triangle replacement. -/
theorem N6_actual_four_clone (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v=3) (loopless : ∀ v,(v,v)∉E)
    {r Q : ℕ} (L : CloneTuple (replacedEdges E cubic) r Q J) (h : feasible L.frame)
    (read : Jet J →ₗ[ℚ] ℚ)
    (correct : ∀ σ, read (nativeScan (replacedEdges E cubic) (replaced_cubic E cubic loopless) L σ).2.2 =
      ∏ e ∈ innerEdges V, pairOR ℚ (σ e.1) (σ e.2))
    (g : Fin r) :
    2^(wholeTriangles (pinGroup L) g).card≤J*Fintype.card (PrivateWord L g) :=
  N6_full_source_fibre L (replaced_cubic E cubic loopless) h read
    (fun σ => (correct σ).trans (UM_is_inner_edges σ).symm) g

#print axioms leftCut_left
#print axioms leftCut_right
#print axioms splice_slice
#print axioms matching_full_rank
#print axioms read_rank
#print axioms finite_private_rank
#print axioms completed_one_active_group
#print axioms N6_group_list
#print axioms N6_full_source_fibre
#print axioms N6_actual_four_clone

end
end V8NativeMessage.N6
