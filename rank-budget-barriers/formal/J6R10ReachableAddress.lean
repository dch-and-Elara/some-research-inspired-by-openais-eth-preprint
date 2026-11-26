import J6R10ReachableDependent

/-! Bring the padded finite alphabet back to the *entire* R9 address
carrier. The correspondence preserves the source centre, binary probe,
group number and generated child record. It is a slot/geometry compiler,
not a proof that raw source data supply its physical child tensors. -/
namespace J6R10Reachable
open J6ActiveRun

universe uh
variable {Host : Type uh}

def addressSigma {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (S : Shape Host Mode) (c : Call Host) :
    Address S c ≃ Σ t : Center S c, Probe S c × Modes S c t × Fin 64 where
  toFun w := ⟨w.t,w.zeta,w.beta,w.group⟩
  invFun w := ⟨w.1,w.2.1,w.2.2.1,w.2.2.2⟩
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

variable (N : NativeShape Host) (B : NativeChildren N) (root : Call Host)
variable [DecidableEq (Envelope N B root)]

noncomputable def nativeAddressEquiv (c : Call Host)
    (hc : NativeReach (nativePlan N B) root c) (ha : N.params.cutoff < c.edges)
    (hw : ∀ t i, 0 < N.weight c t i) :
    NativeAddress N c ≃ Address (paddedShape N B root) c :=
  (Equiv.sigmaCongrRight (fun t : Center N.params c =>
    (Equiv.refl (Probe N.params c)).prodCongr
      ((nativeSlotEquiv N B root c hc ha t (hw t)).prodCongr (Equiv.refl (Fin 64))))).trans
    (addressSigma (paddedShape N B root) c).symm

theorem address_indices (c : Call Host) (hc : NativeReach (nativePlan N B) root c)
    (ha : N.params.cutoff < c.edges) (hw : ∀ t i, 0 < N.weight c t i)
    (w : NativeAddress N c) :
    let decoded := nativeAddressEquiv N B root c hc ha hw w
    decoded.t = w.1 ∧ decoded.zeta = w.2.1 ∧ decoded.group = w.2.2.2 :=
  ⟨rfl,rfl,rfl⟩

noncomputable def widenedChild (c : Call Host) (hc : NativeReach (nativePlan N B) root c)
    (ha : N.params.cutoff < c.edges) (hw : ∀ t i, 0 < N.weight c t i)
    (w : Address (paddedShape N B root) c) : Call Host :=
  (nativePlan N B).child c ⟨(nativeAddressEquiv N B root c hc ha hw).symm w,ha⟩

theorem widenedChild_exact (c : Call Host) (hc : NativeReach (nativePlan N B) root c)
    (ha : N.params.cutoff < c.edges) (hw : ∀ t i, 0 < N.weight c t i)
    (w : NativeAddress N c) :
    widenedChild N B root c hc ha hw (nativeAddressEquiv N B root c hc ha hw w) =
      (nativePlan N B).child c ⟨w,ha⟩ := by
  unfold widenedChild
  rw [Equiv.symm_apply_apply]

theorem widenedChild_size_and_precision (c : Call Host) (hc : NativeReach (nativePlan N B) root c)
    (ha : N.params.cutoff < c.edges) (hw : ∀ t i, 0 < N.weight c t i)
    (w : Address (paddedShape N B root) c) :
    let d := widenedChild N B root c hc ha hw w
    32*d.edges ≤ 3*c.edges ∧ d.depth = c.depth+1 ∧
       d.prec = registerPrecision (paddedShape N B root) c w.t := by
  let v := (nativeAddressEquiv N B root c hc ha hw).symm w
  have ht := (address_indices N B root c hc ha hw v).1
  change (nativeAddressEquiv N B root c hc ha hw v).t = v.1 at ht
  rw [show nativeAddressEquiv N B root c hc ha hw v = w from Equiv.apply_symm_apply _ _] at ht
  exact ⟨B.bound c ha v,rfl,congrArg (registerPrecision N.params c) ht.symm⟩

#print axioms nativeAddressEquiv
#print axioms address_indices
#print axioms widenedChild_exact
#print axioms widenedChild_size_and_precision
end J6R10Reachable