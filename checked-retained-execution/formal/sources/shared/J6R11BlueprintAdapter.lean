import J6R10ReachableAddress
import J6R9RecursiveRun

/-! Bind the exact dependent-slot adapter to the R9 valid-only runner.
Only records reachable from the native root are admitted. This file
does not assume or assert the raw physical probe equality: it transports
that remaining local proof obligation without changing the probe sum. -/
namespace J6R11Blueprint
open scoped BigOperators Polynomial
open J6ActiveRun J6R9Recursive J6R10Reachable

universe uh
variable {Host : Type uh}

theorem nativeReach_trans {C : Type*} (P : FinitePlan C) {a b d : C}
    (h : NativeReach P a b) (k : NativeReach P b d) : NativeReach P a d := by
  induction h with
  | reflexive => exact k
  | step w _ ih => exact NativeReach.step w (ih k)

variable (N : NativeShape Host) (C : NativeChildren N) (r : Call Host)
variable [DecidableEq (Envelope N C r)]

abbrev IsNative (c : Call Host) := NativeReach (nativePlan N C) r c

abbrev PositiveData :=
  ∀ c, IsNative N C r c → N.params.cutoff < c.edges → ∀ t i, 0 < N.weight c t i

variable (hW : PositiveData N C r)

noncomputable def selectedChild (c : Call Host) (w : Address (paddedShape N C r) c) : Call Host := by
  classical
  exact if hc : IsNative N C r c then
    if ha : N.params.cutoff < c.edges then widenedChild N C r c hc ha (hW c hc ha) w
    else ⟨c.host,c.depth+1,0,registerPrecision (paddedShape N C r) c w.t⟩
  else ⟨c.host,c.depth+1,0,registerPrecision (paddedShape N C r) c w.t⟩

theorem selectedChild_exact (c : Call Host) (hc : IsNative N C r c)
    (ha : N.params.cutoff < c.edges) (w : Address (paddedShape N C r) c) :
    selectedChild N C r hW c w = widenedChild N C r c hc ha (hW c hc ha) w := by
  classical
  simp only [selectedChild,dif_pos hc,dif_pos ha]

theorem selectedChild_bound (c : Call Host) (ha : N.params.cutoff < c.edges)
    (w : Address (paddedShape N C r) c) : 32*(selectedChild N C r hW c w).edges ≤ 3*c.edges := by
  classical
  by_cases hc : IsNative N C r c
  · rw [selectedChild_exact N C r hW c hc ha]
    exact (widenedChild_size_and_precision N C r c hc ha (hW c hc ha) w).1
  · simp [selectedChild,hc]

variable (f : ℤ[X]) (ell : ℕ)
variable (entries : ∀ c : Call Host, (Fin c.edges → Bool) → List (IntRing f ell))

noncomputable def paddedBlueprint : Blueprint (paddedShape N C r) f ell where
  childHost := fun c w => (selectedChild N C r hW c w).host
  childEdges := fun c w => (selectedChild N C r hW c w).edges
  edgeBound := selectedChild_bound N C r hW
  entries := entries

theorem paddedBlueprint_child (c : Call Host) (hc : IsNative N C r c)
    (ha : N.params.cutoff < c.edges) (w : Address (paddedShape N C r) c) :
    (paddedBlueprint N C r hW f ell entries).program.child c w =
      widenedChild N C r c hc ha (hW c hc ha) w := by
  let d := widenedChild N C r c hc ha (hW c hc ha) w
  have hh := widenedChild_size_and_precision N C r c hc ha (hW c hc ha) w
  unfold Program.child Blueprint.program paddedBlueprint
  dsimp only
  rw [selectedChild_exact N C r hW c hc ha w]
  change (⟨d.host,c.depth+1,d.edges,registerPrecision (paddedShape N C r) c w.t⟩ : Call Host) = d
  rw [← hh.2.1,← hh.2.2]

theorem paddedBlueprint_closed (c : Call Host) (hc : IsNative N C r c)
    (ha : N.params.cutoff < c.edges) (w : Address (paddedShape N C r) c) :
    IsNative N C r ((paddedBlueprint N C r hW f ell entries).program.child c w) := by
  rw [paddedBlueprint_child N C r hW f ell entries c hc ha w]
  exact nativeReach_trans _ hc (NativeReach.step
    ⟨(nativeAddressEquiv N C r c hc ha (hW c hc ha)).symm w,ha⟩
    (NativeReach.reflexive _))

#print axioms nativeReach_trans
#print axioms paddedBlueprint_child
#print axioms paddedBlueprint_closed
end J6R11Blueprint