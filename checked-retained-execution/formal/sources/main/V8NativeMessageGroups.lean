import V8PooledMenuRoot

/-! N8: split the genuine zero-mode polynomial by the existing group
assignment of the original five-copy network. The C4 whole-input tape
by itself gives no such row restriction. -/
namespace V8NativeMessage
open scoped BigOperators Polynomial Classical
open Polynomial DenominatorBudget V8PooledMenu P11FullPacking J6R10Repack J6R9Recursive
open J6R9PacketScopes J6R10PacketAssembly V8PooledRange V8PooledRange.NativeOrigin

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1700000

variable {W A B G : Type} [Fintype W] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ} {N : Network W A B}

/-- The actual group summand in the whole zero-mode function. No
dependence on foreign input flags is introduced by a polynomial name. -/
def groupPoly (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (g : G)
    (flag : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool) : TwoLocal[X] :=
  ∑ v : PhysicalState P i g, Polynomial.C (oldScalar P i g flag v) *
    ∏ k, ∏ r ∈ actualRows (childBlock P i) g k, affineScaled P i t g v r

theorem group_local (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (g : G)
    (flag flag' : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (h : ∀ (u : A ⊕ B), atGroup P i u=g → ∀ q, flag u q=flag' u q) :
    groupPoly P i t g flag=groupPoly P i t g flag' := by
  unfold groupPoly
  refine Finset.sum_congr rfl (fun v _ => ?_)
  congr 2
  unfold oldScalar
  refine Finset.prod_congr rfl (fun u _ => ?_)
  rw [h u.val u.property]

def partPoly (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (T : Finset G)
    (flag : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool) : TwoLocal[X] :=
  ∏ g ∈ T, groupPoly P i t g flag

theorem part_local (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (T : Finset G)
    (flag flag' : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (h : ∀ (u : A ⊕ B), atGroup P i u ∈ T → ∀ q, flag u q=flag' u q) :
    partPoly P i t T flag=partPoly P i t T flag' := by
  unfold partPoly
  refine Finset.prod_congr rfl (fun g hg => ?_)
  apply group_local
  intro u hu q
  exact h u (hu.symm ▸ hg) q

theorem whole_split (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (T : Finset G)
    (flag : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool) :
    wholeScaled P i t flag=partPoly P i t T flag*partPoly P i t Tᶜ flag :=
  (Finset.prod_mul_prod_compl T (fun g => groupPoly P i t g flag)).symm

namespace Five
open V8PooledMenu.FiveCopy
variable {V E : Type} [Fintype V] [Fintype E] {G₀ : Graph V E} {p : ThreePorts G₀}

def switchVertex (v : V) : RawOld V E ⊕ Occ V E := .inl (.inl (.inl (.inr v)))

/-- The actual coordinate group of the unique old switch clause,
not the group of one of its variables or a new packet seat. -/
def switchGroup (P : Packing G₀ p) (i : Fin (rootA V)) (v : V) : Fin 64 :=
  atGroup P i (switchVertex v)

omit [Fintype V] [Fintype E] in
theorem flags_only_switch (G : Graph V E) (p : ThreePorts G) (s s' : V → Bool)
    (u : RawOld V E ⊕ Occ V E) (q : ParentPorts (network G p) u → Bool)
    (same : ∀ v, u=switchVertex v → s v=s' v) :
    flags G p s u q=flags G p s' u q := by
  rcases u with ((u|v)|q₀)
  · rcases u with ((⟨v,j⟩|v)|(e|⟨⟩))
    · rfl
    · have h : s v=s' v := same v rfl
      simp only [flags,clauses,h]
    · rfl
    · rfl
  · rfl
  · rfl

theorem part_switch_local (P : Packing G₀ p) (i : Fin (rootA V)) (t : ℤ)
    (T : Finset (Fin 64)) (s s' : V → Bool)
    (same : ∀ v, switchGroup P i v∈T → s v=s' v) :
    partPoly P i t T (flags G₀ p s)=partPoly P i t T (flags G₀ p s') := by
  apply part_local
  intro u hu q
  apply flags_only_switch
  intro v hv
  apply same
  change atGroup P i (switchVertex v)∈T
  rw [← hv]
  exact hu

#print axioms group_local
#print axioms part_local
#print axioms whole_split
#print axioms flags_only_switch
#print axioms part_switch_local
end Five
end
end V8NativeMessage
