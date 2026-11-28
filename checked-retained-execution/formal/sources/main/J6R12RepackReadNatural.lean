import J6R12RepackBoolean
import J6R9RecursiveProbes

/-! Read a known-small constant natural number from the actual native
doubly adjoined receiver. This is not a lift of arbitrary arithmetic:
the upper bound below is used exactly at the final ZMod val step. -/
namespace J6R12Repack
open scoped Polynomial
open Polynomial J6R9Recursive

private theorem monic_rep_const {A : Type*} [CommRing A] [Nontrivial A]
    (Q : A[X]) (hQ : Q.Monic) (hpos : 0<Q.natDegree) (x : A) :
    AdjoinRoot.modByMonicHom hQ (AdjoinRoot.mk Q (C x)) = C x := by
  rw [AdjoinRoot.modByMonicHom_mk]
  apply (modByMonic_eq_self_iff hQ).mpr
  have hn : Q≠0 := by intro h; simp [h] at hpos
  apply degree_C_le.trans_lt
  rw [degree_eq_natDegree hn]
  exact_mod_cast hpos

private theorem monic_rep_nat {A : Type*} [CommRing A] [Nontrivial A]
    (Q : A[X]) (hQ : Q.Monic) (hpos : 0<Q.natDegree) (n : ℕ) :
    (AdjoinRoot.modByMonicHom hQ (n:AdjoinRoot Q)).coeff 0 = n := by
  have h : (n:AdjoinRoot Q) = AdjoinRoot.mk Q (C (n:A)) := by simp
  rw [h,monic_rep_const Q hQ hpos,coeff_C_zero]

noncomputable def boxNatural (f : ℤ[X]) (ell p : ℕ) (hf : f.Monic)
    (x : Box f ell p) : ℕ :=
  ((AdjoinRoot.modByMonicHom (hf.map (Int.castRingHom (NativeProbeRing.Base p)))
      ((AdjoinRoot.modByMonicHom (monic_X.pow ell) x).coeff 0)).coeff 0).val

theorem boxNatural_of_nat (f : ℤ[X]) (ell p : ℕ) (hf : f.Monic)
    (hp : 0<p) (hℓ : 0<ell) (hd : 0<f.natDegree) (n : ℕ) (hn : n<2^p) :
    boxNatural f ell p hf (n:Box f ell p) = n := by
  letI : Fact (1 < (2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  let F := f.map (Int.castRingHom (NativeProbeRing.Base p))
  have hmon : F.Monic := hf.map _
  have hdeg : 0<F.natDegree := (hf.natDegree_map (Int.castRingHom (NativeProbeRing.Base p))).symm ▸ hd
  have hnt : (1:NativeProbeRing.Scalar p f)≠0 := by
    intro h
    have h1 : (AdjoinRoot.modByMonicHom hmon (1:NativeProbeRing.Scalar p f)).coeff 0 =
      (1:NativeProbeRing.Base p) := by
      simpa only [Nat.cast_one] using (monic_rep_nat F hmon hdeg 1)
    rw [h,map_zero,coeff_zero] at h1
    exact zero_ne_one h1
  letI : Nontrivial (NativeProbeRing.Scalar p f) := ⟨⟨1,0,hnt⟩⟩
  have hpow : 0<((X:(NativeProbeRing.Scalar p f)[X])^ell).natDegree := by
    rw [natDegree_X_pow]
    exact hℓ
  unfold boxNatural
  rw [monic_rep_nat _ (monic_X.pow ell) hpow n,
    monic_rep_nat F hmon hdeg n]
  exact ZMod.val_natCast_of_lt hn

#print axioms boxNatural
#print axioms boxNatural_of_nat
end J6R12Repack
