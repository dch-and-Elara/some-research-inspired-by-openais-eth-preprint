import P5A11JetCoordinate

/-! The literal projection from k coefficients to l coefficients;
its kernel is the image of multiplication by the true root to the
l-th power, not an abstract cokernel receipt. -/
namespace Paper5
open Polynomial Matrix
open scoped BigOperators Polynomial Classical
variable {S : Type*} [CommRing S]

theorem sharp_plain_root_nil (k : ℕ) :
    (AdjoinRoot.root (X^k : S[X]))^k=0 := by
  change (AdjoinRoot.mk (X^k) X : PlainJet S k)^k=0
  rw [←map_pow,AdjoinRoot.mk_self]

noncomputable def sharpJetProjection (k l : ℕ) (hl : l≤k) :
    PlainJet S k →ₐ[S] PlainJet S l :=
  AdjoinRoot.liftHom (X^k) (AdjoinRoot.root (X^l))
    (by
      rw [map_pow,aeval_X]
      obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hl
      rw [pow_add,sharp_plain_root_nil l,zero_mul])

theorem sharpJetProjection_mk (k l : ℕ) (hl : l≤k) (p : S[X]) :
    sharpJetProjection (S:=S) k l hl (AdjoinRoot.mk (X^k) p) =
      AdjoinRoot.mk (X^l) p := by
  unfold sharpJetProjection
  rw [AdjoinRoot.liftHom_mk,AdjoinRoot.aeval_eq]

theorem sharpJetProjection_surjective (k l : ℕ) (hl : l≤k) :
    Function.Surjective (sharpJetProjection (S:=S) k l hl) := by
  intro x
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
  exact ⟨AdjoinRoot.mk (X^k) p,sharpJetProjection_mk k l hl p⟩

theorem sharpJetProjection_root_range (k l : ℕ) (hl : l≤k) (x : PlainJet S k) :
    sharpJetProjection (S:=S) k l hl x=0 ↔
      ∃ y : PlainJet S k,(AdjoinRoot.root (X^k : S[X]))^l*y=x := by
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
  constructor
  · intro h
    rw [sharpJetProjection_mk,AdjoinRoot.mk_eq_zero] at h
    obtain ⟨q,rfl⟩ := h
    refine ⟨AdjoinRoot.mk (X^k) q,?_⟩
    change (AdjoinRoot.mk (X^k) X)^l*AdjoinRoot.mk (X^k) q=_
    rw [map_mul,map_pow]
  · rintro ⟨y,hy⟩
    rw [←hy,map_mul,map_pow]
    change (AdjoinRoot.liftHom _ _ _) (AdjoinRoot.root (X^k : S[X])) ^ l *
      sharpJetProjection (S:=S) k l hl y=0
    rw [AdjoinRoot.liftHom_root,sharp_plain_root_nil l,zero_mul]

theorem sharpJetProjection_scaled_range (k l : ℕ) (hl : l≤k)
    (v : (PlainJet S k)ˣ) (x : PlainJet S k) :
    sharpJetProjection (S:=S) k l hl x=0 ↔
      ∃ y : PlainJet S k,((v:PlainJet S k)*(AdjoinRoot.root (X^k : S[X]))^l)*y=x := by
  rw [sharpJetProjection_root_range]
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨(↑v⁻¹:PlainJet S k)*y,?_⟩
    rw [←hy]
    calc
      _ = ((v:PlainJet S k)*(↑v⁻¹:PlainJet S k))*((AdjoinRoot.root (X^k : S[X]))^l*y) := by ring
      _ = _ := by rw [Units.mul_inv,one_mul]
  · rintro ⟨y,hy⟩
    refine ⟨(v:PlainJet S k)*y,?_⟩
    rw [←hy]
    ring

#print axioms sharpJetProjection_surjective
#print axioms sharpJetProjection_root_range
#print axioms sharpJetProjection_scaled_range
end Paper5
