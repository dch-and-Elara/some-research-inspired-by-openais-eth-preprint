import J6R15SpecializedBoxNativeKernel
import J9R13PhysicalFusion
import J6R14SpecializedBoxPreservedMode
import J6R10RowIdentity

/-! At the selected same physical address, R13's crossing function
equals the true R12 scaled mode on *every real row port*, including
the zero assigned outside the eligible target fibre. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6R9PacketScopes J6R9PacketChild J6R9PacketCoeff
open J6R9Recursive J8Physical J8EndToEnd J8J9Grouped NativeProbeRing DyadicProbeCompiler

noncomputable section
variable {G R S V : Type*} [LinearOrder G] {P : V→Type*} {a b : ℕ}
variable (d : Layout (Page a b G) R S V G P (2^a))
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype (Page a b G)]
variable [(v : V)→Fintype (P v)] [(v : V)→DecidableEq (P v)]
variable (mask : MaskFamily a b G) (i : Fin a)
variable (hr : ∀ x, rowGroup mask i (d.seat x) = d.rowLabel x.1)
variable (hc : ∀ x, colGroup mask i (d.seat x) = actualColLabel d x)

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 2000000 in
theorem actual_scaled_cross_all_ports (hi : i.val=0) (p ell : ℕ) (hp : 0<p) (f : ℤ[X])
    (hnil : (2:Box f ell p)^p=0) (z : Scalar p f)
    (he : Even (2^a:ℕ)) (hL : 2<(2^a:ℕ)) (s : S)
    (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (n : ℕ) (hN : n<p-1)
    (ht : ((2^a:ℕ):ℤ)-1≠0) (hv : padicValInt 2 (((2^a:ℕ):ℤ)-1)=i.val)
    (x : Wire R) :
    let m := anchoredMode d mask i hr hc s off (⟨n,hN⟩:Fin (p-1))
    let v := J6ActiveInterpolation.scalarIn p f ell z
    J6R10RowIdentity.scaledRow mask i ht hv p hnil v (d.seat x) m =
      (2:Box f ell p)^(a+1+n)*v *
        evalBox p f ell z (J9R13GroupFusion.targetKernel (groupedTargets d s)
          (fun j : TargetPorts d s => (j.1.1,j.2))
          (physicalKernel d s he hL (J9FactorBounds.kernel (2^a)) n
            (fun j => (genuineCross d a p n he hL s j).divX)) x) := by
  rcases i with ⟨vI,hI⟩
  change vI=0 at hi
  subst vI
  let i : Fin a := ⟨0,hI⟩
  let m := anchoredMode d mask i hr hc s off (⟨n,hN⟩:Fin (p-1))
  let v := J6ActiveInterpolation.scalarIn p f ell z
  let Q := physicalKernel d s he hL (J9FactorBounds.kernel (2^a)) n
    (fun j => (genuineCross d a p n he hL s j).divX)
  change J6R10RowIdentity.scaledRow mask i ht hv p hnil v (d.seat x) m =
    (2:Box f ell p)^(a+1+n)*v *
      evalBox p f ell z (J9R13GroupFusion.targetKernel (groupedTargets d s)
        (fun j : TargetPorts d s => (j.1.1,j.2)) Q x)
  have chart := anchored_actual_target_iff d mask i hr hc rfl s off ⟨n,hN⟩ x
  simp only [targets,Finset.mem_filter,Finset.mem_univ,true_and] at chart
  by_cases h : rowBlock mask i (d.seat x)=target mask i m
  · have hg := congrArg Prod.snd (h.trans (anchored_target d mask i hr hc s off ⟨n,hN⟩))
    change rowGroup mask i (d.seat x)=d.rowLabel (pinWire d s).1 at hg
    rw [hr x] at hg
    let j : TargetPorts d s := (⟨x.1,hg⟩,x.2)
    have hj : j∈groupedTargets d s :=
      by simpa only [groupedTargets,targets,Finset.mem_filter,Finset.mem_univ,true_and,j] using (chart.mp h)
    have hKernel : J9R13GroupFusion.targetKernel (groupedTargets d s)
        (fun j : TargetPorts d s => (j.1.1,j.2)) Q x = Q j := by
      unfold J9R13GroupFusion.targetKernel
      rw [Finset.sum_eq_single_of_mem j hj]
      · rw [if_pos (show (j.1.1,j.2)=x by cases x; rfl)]
      · intro j' _ hne
        apply if_neg
        intro hh
        apply hne
        exact Prod.ext (Subtype.ext (congrArg (fun w : Wire R => w.1) hh))
          (congrArg (fun w : Wire R => w.2) hh)
    rw [hKernel,J6R10RowIdentity.scaledRow,on_target_exact mask i ht hv p hnil v (d.seat x) m h]
    exact literal_target_mode_at_probe d a p hp rfl he hL s n j hj _ f ell hnil z
  · have hz : J9R13GroupFusion.targetKernel (groupedTargets d s)
        (fun j : TargetPorts d s => (j.1.1,j.2)) Q x = 0 := by
      unfold J9R13GroupFusion.targetKernel
      apply Finset.sum_eq_zero
      intro j hj
      apply if_neg
      intro eq
      apply h
      apply chart.mpr
      simp only [groupedTargets,targets,Finset.mem_filter,Finset.mem_univ,true_and] at hj
      exact eq ▸ hj
    rw [hz,map_zero,mul_zero,J6R10RowIdentity.scaledRow,off_target mask i ht hv p hnil v (d.seat x) m h,mul_zero]

#print axioms actual_scaled_cross_all_ports
end
end J6R14SpecializedBox