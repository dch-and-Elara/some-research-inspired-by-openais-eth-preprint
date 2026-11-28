import P5OuterCenterFactors
import P5OuterCenterRootExact
import P5OuterCenterCloneRoot
set_option warningAsError true
set_option maxHeartbeats 2500000
namespace Paper5.OuterCenters.Factors
open scoped BigOperators Classical Polynomial
open P11FullPacking J6R10Repack J6R9PacketScopes HybridClosure HybridDUncloned D1Literal
  J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R9Recursive

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (base : ∀ v, GraphCutMoments.degree E v = 3)
variable (F : Finset (TriVertex V × TriVertex V))
variable (cub : ∀ v, GraphCutMoments.degree F v = 3)
variable (hF : F = replacedEdges E base)
variable (loopless : ∀ v, (v,v) ∉ E)
local notation "W" => TriVertex V

/-- The two terminal products are ordered as triangle then exterior. -/
noncomputable def factorPair (σ : W → Bool) : ℕ × ℕ :=
  ((∏ e ∈ innerEdges V, edgeOr σ e), (∏ e ∈ outerEdges E base, edgeOr σ e))

include hF in
theorem interior_edge_in_actual_graph (x : W) :
    (x,innerMate V x) ∈ F ∨ (innerMate V x,x) ∈ F := by
  rw [hF]
  exact innerMate_exact_graph E base x

include hF loopless in
theorem uncloned_both_isolated_native_fibers
    (P : PhysicalPacking (network F cub) (rootBits (sourceSize F)) (Fin 64))
    (K : ℕ) (hK : 1024*K ≤ 2^rootBits (sourceSize F))
    (hn : 0 < Fintype.card (W)) (f : ℤ[X]) (hf : f.Monic)
    (d : Ready (printedParams (f:=f) (ell:=1) (sourceSize F))
      (J1PPrinted.sourceDelta (sourceSize F)) (root F cub f (fun _ => true))) :
    let c₀ := root F cub f (fun _ => true)
    let S := printedParams (f:=f) (ell:=1) (sourceSize F)
    let one : W → Bool := fun _ => true
    let witness (out : ℕ × ℕ) : Prop :=
      ∃ x y : W,
        let σ := one
        let τ := signsWithTwoZero x y
        PinnedCNF.modelCount (PinnedCNF.formula F σ) = 1 ∧
        PinnedCNF.modelCount (PinnedCNF.formula F τ) = 0 ∧
        factorPair E base σ = (1,1) ∧ factorPair E base τ = out ∧
        ∀ (t : Center S c₀)
          (β : Mode (centerIndex d t) (registerPrecision S c₀ t) P.mask →₀ ℕ)
          (g : Fin 64),
          (((2^rootBits (sourceSize F) : ℕ) : ℤ) - K ≤ t.val ∨
            t.val ≤ -(((2^rootBits (sourceSize F) : ℕ) : ℤ) - K)) →
          @nativeRead (W) _ _ F cub (Fin 64) _ _ (rootBits (sourceSize F)) P (centerIndex d t) t.val (centerNonzero t) rfl c₀.prec
            (registerPrecision S c₀ t) f hf
            (J6R10Integral.box_two_nil (registerPrecision S c₀ t) f 1) σ β g =
          @nativeRead (W) _ _ F cub (Fin 64) _ _ (rootBits (sourceSize F)) P (centerIndex d t) t.val (centerNonzero t) rfl c₀.prec
            (registerPrecision S c₀ t) f hf
            (J6R10Integral.box_two_nil (registerPrecision S c₀ t) f 1) τ β g
    witness (0,1) ∧ witness (1,0) := by
  have hall : factorPair E base (fun _ => true) = (1,1) :=
    Prod.ext (factor_all_one _) (factor_all_one _)
  have hi := Paper5.OuterCenters.every_source_outer_zero_child F cub (innerMate V)
    (interior_edge_in_actual_graph E base F hF) P K hK hn f hf d
  have he := Paper5.OuterCenters.every_source_outer_zero_child F cub (exteriorMate E base)
    (exteriorMate_exact_graph E base F hF) P K hK hn f hf d
  obtain ⟨x,hx₁,hx₀,hx⟩ := hi
  obtain ⟨y,hy₁,hy₀,hy⟩ := he
  have fi := triangle_flip_isolates_triangle_factor E base loopless x
  have fe := exterior_flip_isolates_exterior_factor E base loopless y
  exact ⟨⟨x,innerMate V x,hx₁,hx₀,hall,Prod.ext fi.1 fi.2,hx⟩,
    ⟨y,exteriorMate E base y,hy₁,hy₀,hall,Prod.ext fe.1 fe.2,hy⟩⟩

include hF loopless in
theorem cloned_both_isolated_native_fibers
    (P : PhysicalPacking (dNetwork F cub) (rootBits (oldRowSize F)) (Fin 64))
    (K : ℕ) (hK : 1024*K ≤ 2^rootBits (oldRowSize F))
    (hn : 0 < Fintype.card (W)) (f : ℤ[X]) (hf : f.Monic)
    (d : Ready (printedParams (f:=f) (ell:=1) (oldRowSize F))
      (J1PPrinted.sourceDelta (oldRowSize F)) (oldRowRoot F cub f (fun _ => true))) :
    let c₀ := oldRowRoot F cub f (fun _ => true)
    let S := printedParams (f:=f) (ell:=1) (oldRowSize F)
    let one : W → Bool := fun _ => true
    let witness (out : ℕ × ℕ) : Prop :=
      ∃ x y : W,
        let σ := one
        let τ := signsWithTwoZero x y
        let CNF := MainClonedCNF.formula F (MainClonedCNF.leftSlot F cub) (MainClonedCNF.rightSlot F cub)
        PinnedCNF.modelCount (CNF σ) = 1 ∧ PinnedCNF.modelCount (CNF τ) = 0 ∧
        factorPair E base σ = (1,1) ∧ factorPair E base τ = out ∧
        ∀ (t : Center S c₀)
          (β : Mode (centerIndex d t) (registerPrecision S c₀ t) P.mask →₀ ℕ)
          (g : Fin 64),
          (((2^rootBits (oldRowSize F) : ℕ) : ℤ) - K ≤ t.val ∨
            t.val ≤ -(((2^rootBits (oldRowSize F) : ℕ) : ℤ) - K)) →
          @Cloned.nativeRead (W) _ _ F cub (Fin 64) _ _ (rootBits (oldRowSize F)) P (centerIndex d t) t.val (centerNonzero t) rfl c₀.prec
            (registerPrecision S c₀ t) f hf
            (J6R10Integral.box_two_nil (registerPrecision S c₀ t) f 1) σ β g =
          @Cloned.nativeRead (W) _ _ F cub (Fin 64) _ _ (rootBits (oldRowSize F)) P (centerIndex d t) t.val (centerNonzero t) rfl c₀.prec
            (registerPrecision S c₀ t) f hf
            (J6R10Integral.box_two_nil (registerPrecision S c₀ t) f 1) τ β g
    witness (0,1) ∧ witness (1,0) := by
  have hall : factorPair E base (fun _ => true) = (1,1) :=
    Prod.ext (factor_all_one _) (factor_all_one _)
  have hi := Cloned.every_source_outer_zero_child F cub (innerMate V)
    (interior_edge_in_actual_graph E base F hF) P K hK hn f hf d
  have he := Cloned.every_source_outer_zero_child F cub (exteriorMate E base)
    (exteriorMate_exact_graph E base F hF) P K hK hn f hf d
  obtain ⟨x,hx₁,hx₀,hx⟩ := hi
  obtain ⟨y,hy₁,hy₀,hy⟩ := he
  have fi := triangle_flip_isolates_triangle_factor E base loopless x
  have fe := exterior_flip_isolates_exterior_factor E base loopless y
  exact ⟨⟨x,innerMate V x,hx₁,hx₀,hall,Prod.ext fi.1 fi.2,hx⟩,
    ⟨y,exteriorMate E base y,hy₁,hy₀,hall,Prod.ext fe.1 fe.2,hy⟩⟩

#print axioms uncloned_both_isolated_native_fibers
#print axioms cloned_both_isolated_native_fibers
end Paper5.OuterCenters.Factors

