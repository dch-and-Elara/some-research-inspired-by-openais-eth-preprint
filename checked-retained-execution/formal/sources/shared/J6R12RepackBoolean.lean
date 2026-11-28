import J6R11RepackRootEntry
import J6R9RecursiveCanonical

/-! Boolean tensors at the actual planted root really lift to 0 or 1 in
the two-local integral algebra. The proof applies only to these two
entries, and never asserts a lifting ring homomorphism. -/
namespace J6R12Repack
open scoped Polynomial
open Polynomial DenominatorBudget J6R9Recursive
open J6R11Repack J6R10Repack J6OrientedHost

private theorem section_one {A B : Type*} [CommRing A] [CommRing B] [Nontrivial B]
    (L : B → A) :
    polynomialSection L (1:B[X]) = C (L 1) := by
  have hs : support (1:B[X]) = {0} := by
    simpa only [map_one] using (support_C (a:=(1:B)) one_ne_zero)
  simp [polynomialSection,hs]

private theorem monic_rep_one {A : Type*} [CommRing A] [Nontrivial A]
    (Q : A[X]) (hQ : Q.Monic) (hpos : 0<Q.natDegree) :
    AdjoinRoot.modByMonicHom hQ (1:AdjoinRoot Q)=1 := by
  rw [← map_one (AdjoinRoot.mk Q),AdjoinRoot.modByMonicHom_mk]
  apply (modByMonic_eq_self_iff hQ).mpr
  rw [degree_one,degree_eq_natDegree hQ.ne_zero]
  exact_mod_cast hpos

theorem canonical_scalar_one (p : ℕ) (hp : 0<p) (f : ℤ[X]) (hf : f.Monic)
    (hpos : 0<f.natDegree) :
    canonicalScalar p f hf (1:NativeProbeRing.Scalar p f) = 1 := by
  letI : Fact (1<(2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  have hdeg : 0<(f.map (Int.castRingHom (NativeProbeRing.Base p))).natDegree :=
    (hf.natDegree_map (Int.castRingHom (NativeProbeRing.Base p))).symm ▸ hpos
  have hB : finiteCoeffLift p (1:NativeProbeRing.Base p)=1 := by
    unfold finiteCoeffLift
    rw [ZMod.val_one]
    simp
  unfold canonicalScalar
  rw [monic_rep_one (f.map (Int.castRingHom (NativeProbeRing.Base p))) (hf.map _) hdeg,section_one,hB,AdjoinRoot.mk_C,map_one]

theorem canonical_lift_zero (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ) :
    canonicalLift p f hf ell 0=0 := by
  simp [canonicalLift,polynomialSection]

theorem canonical_lift_one (p : ℕ) (hp : 0<p) (f : ℤ[X]) (hf : f.Monic)
    (hpos : 0<f.natDegree) (ell : ℕ) (hℓ : 0<ell) :
    canonicalLift p f hf ell 1=1 := by
  letI : Fact (1<(2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  have hdeg : 0<(f.map (Int.castRingHom (NativeProbeRing.Base p))).natDegree :=
    (hf.natDegree_map (Int.castRingHom (NativeProbeRing.Base p))).symm ▸ hpos
  have hn : (1:NativeProbeRing.Scalar p f)≠0 := by
    intro h
    apply (one_ne_zero : (1:(NativeProbeRing.Base p)[X])≠0)
    have hh := congrArg (AdjoinRoot.modByMonicHom
      (hf.map (Int.castRingHom (NativeProbeRing.Base p)))) h
    rw [monic_rep_one (f.map (Int.castRingHom (NativeProbeRing.Base p))) (hf.map _) hdeg,map_zero] at hh
    exact hh
  letI : Nontrivial (NativeProbeRing.Scalar p f) := ⟨⟨1,0,hn⟩⟩
  have hdegree : 0<((X:(NativeProbeRing.Scalar p f)[X])^ell).natDegree := by
    rw [natDegree_X_pow]
    exact hℓ
  unfold canonicalLift
  rw [monic_rep_one ((X:(NativeProbeRing.Scalar p f)[X])^ell) (monic_X.pow _) hdegree,
      section_one,canonical_scalar_one p hp f hf hpos,
      AdjoinRoot.mk_C,map_one]

theorem canonical_lift_bool (p : ℕ) (hp : 0<p) (f : ℤ[X]) (hf : f.Monic)
    (hpos : 0<f.natDegree) (ell : ℕ) (hℓ : 0<ell) (b : Bool) :
    canonicalLift p f hf ell (if b then 1 else 0) = if b then 1 else 0 := by
  cases b
  · exact canonical_lift_zero p f hf ell
  · exact canonical_lift_one p hp f hf hpos ell hℓ

variable {S V : Type*} [LinearOrder S] {a b m q l : ℕ}

theorem actual_root_table_integral (f : ℤ[X]) (ell p : ℕ) (T : Plant V m q)
    (w : Fin a → S) (hf : f.Monic) (hp : 0<p) (hd : 0<f.natDegree) (hℓ : 0<ell)
    (x : Wire w m b l → Bool) (v : Left V w m b l ⊕ Right w m b l q) :
    (rootEntryFile f ell p T w v).frozen hf (assignment (rootNetwork T w) x v) =
      if rootFlag T w x v then 1 else 0 := by
  cases v with
  | inl v => exact canonical_lift_bool p hp f hf hd ell hℓ _
  | inr v => exact canonical_lift_bool p hp f hf hd ell hℓ _

#print axioms canonical_scalar_one
#print axioms canonical_lift_zero
#print axioms canonical_lift_one
#print axioms canonical_lift_bool
#print axioms actual_root_table_integral
end J6R12Repack
