import J6R11BlueprintAdapter

/-! Exact per-probe grouped callback transport through the native menu. -/
namespace J6R11Blueprint
open scoped BigOperators Polynomial
open J6ActiveRun J6R9Recursive J6R10Reachable

noncomputable def blueprintReplies {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    {S : Shape Host Mode} {f : ℤ[X]} {ell : ℕ}
    (B : Blueprint S f ell) (c : Call Host) : Responses S f ell c :=
  fun w => B.expect (B.program.child c w)

universe uh
variable {Host : Type uh}
variable (N : NativeShape Host) (C : NativeChildren N) (r : Call Host)
variable [DecidableEq (Envelope N C r)]
variable (hW : PositiveData N C r) (f : ℤ[X]) (ell : ℕ)
variable (entries : ∀ c : Call Host, (Fin c.edges → Bool) → List (IntRing f ell))

noncomputable def nativeMenuFinite (c : Call Host) (t : Center N.params c) :
    Fintype (NativeMenu N c t) :=
  Finset.fintypeCoeSort (@J6RecursiveMenu.menu (N.Mode c t) (N.finiteMode c t)
    (N.decideMode c t) (registerPrecision N.params c t) (N.weight c t))

noncomputable def nativeGrouped (c : Call Host) (ha : N.params.cutoff < c.edges)
    (t : Center N.params c) (z : Probe N.params c) :
    Box f ell (registerPrecision N.params c t) := by
  letI := nativeMenuFinite N c t
  exact ∑ β : NativeMenu N c t, ∏ g : Fin 64,
    reduce (registerPrecision N.params c t) f ell
      ((paddedBlueprint N C r hW f ell entries).truth ((nativePlan N C).child c ⟨⟨t,z,β,g⟩,ha⟩))

set_option maxHeartbeats 5500000 in
noncomputable def paddedGroupedAt (c : Call Host) (t : Center N.params c)
    (z : Probe N.params c) : Box f ell (registerPrecision N.params c t) :=
  @groupedSample Host (Envelope N C r) (envelopeFinite N C r) _
    (paddedShape N C r) f ell c
    (@blueprintReplies Host (Envelope N C r) (envelopeFinite N C r) _
      (paddedShape N C r) f ell (paddedBlueprint N C r hW f ell entries) c) t z

set_option maxHeartbeats 5500000 in
theorem paddedBlueprint_grouped (c : Call Host) (hc : IsNative N C r c)
    (ha : N.params.cutoff < c.edges) (t : Center N.params c) (ζ : Probe N.params c) :
    paddedGroupedAt N C r hW f ell entries c t ζ =
      nativeGrouped N C r hW f ell entries c ha t ζ := by
  let B := paddedBlueprint N C r hW f ell entries
  unfold paddedGroupedAt nativeGrouped groupedSample
  symm
  apply Fintype.sum_equiv (nativeSlotEquiv N C r c hc ha t (hW c hc ha t))
  intro β
  apply Finset.prod_congr rfl
  intro g _
  let addr : NativeAddress N c := ⟨t,ζ,β,g⟩
  let w := nativeAddressEquiv N C r c hc ha (hW c hc ha) addr
  change reduce (registerPrecision N.params c t) f ell
    (B.truth ((nativePlan N C).child c ⟨addr,ha⟩)) =
      reduce (registerPrecision N.params c t) f ell (B.truth (B.program.child c w))
  rw [paddedBlueprint_child N C r hW f ell entries c hc ha w,
    show w = nativeAddressEquiv N C r c hc ha (hW c hc ha) addr from rfl,
    widenedChild_exact N C r c hc ha (hW c hc ha) addr]

#print axioms paddedBlueprint_grouped
end J6R11Blueprint