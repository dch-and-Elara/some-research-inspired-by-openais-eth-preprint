import J3R60Clearing
import J3R38LiteralSingletonHeight

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-! The real row bounds from v8 N1 control both private native readout
and the public normalization pieces of v9 J3. -/
namespace J3R60
open Polynomial V8NativeMessage V8NativeMessage.C3.NativeAssembly.MainScan
open V8NativeMessage.N6.MainFiber
open J3R38LiteralSingleton
open scoped Classical BigOperators Polynomial

theorem inputHeight_mono {B B' : ℕ} {q : ℚ} (h : B ≤ B') (hq : inputHeight B q) :
    inputHeight B' q := by
  have hp : 2^B ≤ 2^B' := Nat.pow_le_pow_right (by decide) h
  exact ⟨hq.1.trans hp, hq.2.trans hp⟩

def publicHeight (W : Type*) [Fintype W] (R Q BP : ℕ) :=
  4*Fintype.card W + (Nat.log 2 (N1.A W R Q BP)+1)*(12*Fintype.card W+1)+1

noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

omit [DecidableEq W] in
theorem source_within_to_public {q : ℚ} {D : ℕ}
    (hd : D ≤ 12*Fintype.card W+1)
    (hq : q.den ∣ (N1.δ R Q)^D)
    (hn : q.num.natAbs ≤ (N1.A W R Q BP)^D) :
    inputHeight (publicHeight W R Q BP) q := by
  have hb := N1.bits_of_bounds (N1.δ_pos R Q) (N1.δ_le_base (W:=W) (BP:=BP))
    (Nat.lt_pow_succ_log_self (by decide) _).le hq
    (by simpa only [Nat.pow_zero,one_mul] using hn :
      q.num.natAbs ≤ 2^0 * N1.A W R Q BP^D)
  apply inputHeight_mono (B := 0+(Nat.log 2 (N1.A W R Q BP)+1)*D+1)
  · unfold publicHeight
    have h := Nat.mul_le_mul_left (Nat.log 2 (N1.A W R Q BP)+1) hd
    omega
  · exact ⟨hb.1.le, hb.2.le⟩

theorem row_at_one_public_height (L : CloneTuple F r Q J)
    (bounds : N1.RowBound L hreg R BP) (o : N1.Occ F) (k : Fin J) :
    inputHeight (publicHeight W R Q BP) ((rowAtOne L hreg o).coeff k.val) := by
  let q : Jet J := AdjoinRoot.mk ((X : ℚ[X])^J) (rowAtOne L hreg o)
  have hq : q = θ L (fun _=>true) (N1.occClause o) (N1.occVar hreg o) :=
    N1.thetaPoly_mk L hreg _ o
  have hL := N1.jetify_iTheta L hreg bounds (fun _=>true) o
  rw [← hq] at hL
  obtain ⟨hd,hn⟩ := N1.integral_jet_height J k.val (N1.δ R Q)
    k.isLt (N1.δ_pos R Q) q _ hL
  have hEq : N1.jetCoeff J k.val q = (rowAtOne L hreg o).coeff k.val :=
    jetCoeff_mk k.isLt _
  rw [hEq] at hd hn
  exact source_within_to_public (W:=W) (D:=1) (by omega)
    (by simpa only [pow_one] using hd)
    (by
      apply hn.trans ((N1.norm_iTheta L hreg bounds _ o).trans ?_)
      simp only [pow_one,N1.A,N1.B₀]
      omega)

theorem background_public_height (L : CloneTuple F r Q J)
    (bounds : N1.RowBound L hreg R BP) (k : Fin J) :
    inputHeight (publicHeight W R Q BP) ((backgroundPoly L hreg).coeff k.val) := by
  let D := ∑ f : F ⊕ Clone W, N1.arity (.inr f)
  have hD : D ≤ 12*Fintype.card W+1 := by
    have hdeg := N1.native_degree hreg
    rw [Fintype.sum_sum_type] at hdeg
    change (∑ f : W, N1.arity (.inl f : Clause F)) + D = _ at hdeg
    omega
  let p : ℤ[X] := ∏ f : F ⊕ Clone W,
    N1.intFactor L hreg bounds (fun _=>false) (fun _=>true) (.inr f)
  let q : Jet J := AdjoinRoot.mk ((X : ℚ[X])^J) (backgroundPoly L hreg)
  have hInt : N1.jetify J p = (N1.δ R Q : Jet J)^D*q := by
    dsimp only [p,q,D]
    simp only [backgroundPoly,map_prod,N1.jetify_factor,Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro f _
    rcases f with (e|i) <;>
      simp [publicFactor,rowAtOne,N1.thetaPoly_mk,cloneFactor,N1.occClause,N1.occVar]
  have hn : N1.coeffNorm p ≤ N1.A W R Q BP^D := by
    unfold p D
    apply (N1.norm_prod _ _).trans
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' (fun f _ => N1.norm_factor L hreg bounds
      (fun _=>true) (fun _=>false) (.inr f))
  have hEq : N1.jetCoeff J k.val q = (backgroundPoly L hreg).coeff k.val :=
    jetCoeff_mk k.isLt _
  have hp : N1.jetify J p = (((N1.δ R Q)^D : ℕ) : Jet J)*q := by
    simpa only [Nat.cast_pow] using hInt
  obtain ⟨hd,hnum⟩ := N1.integral_jet_height J k.val ((N1.δ R Q)^D)
    k.isLt (Nat.pow_pos (N1.δ_pos R Q)) q p hp
  rw [hEq] at hd hnum
  exact source_within_to_public (W:=W) hD hd (hnum.trans hn)

/-- All six types of actual arguments of the original normalized equation,
starting from the printed replacement row statement. -/
theorem original_J3_primitives_height (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (hr : 2 ≤ r) (hR : 1 ≤ R) (hfit : 6*R ≤ Q)
    (a : Address W Q) (s : W → Bool)
    (bounds : N1.RowBound (literalTuple P R hJ Prow a) hreg R BP) :
    let B := publicHeight W R Q BP
    inputHeight B (jetCoeff 0 (rawJet P R hJ Prow a s)) ∧
    inputHeight B (jetCoeff 1 (rawJet P R hJ Prow a s)) ∧
    inputHeight B (backgroundConstant hreg Prow a.1) ∧
    inputHeight B ((backgroundPoly (literalTuple P R hJ Prow a) hreg).coeff 1) ∧
    (∀ v, inputHeight B (pinConstant hreg Prow a.1 v)) ∧
    (∀ v, inputHeight B (pinDerivative hreg Prow a v)) := by
  dsimp only
  let L := literalTuple P R hJ Prow a
  let i0 : Fin J := ⟨0,by omega⟩
  let i1 : Fin J := ⟨1,by omega⟩
  have hSource : 4*Fintype.card W+
      (Nat.log 2 (N1.A W R Q BP)+1)*(12*Fintype.card W)+1 ≤ publicHeight W R Q BP := by
    unfold publicHeight
    have hh := Nat.mul_le_mul_left (Nat.log 2 (N1.A W R Q BP)+1)
      (Nat.le_succ (12*Fintype.card W))
    exact Nat.add_le_add_right (Nat.add_le_add_left hh _) _
  have raw (k : Fin J) : inputHeight (publicHeight W R Q BP)
      (jetCoeff k.val (rawJet P R hJ Prow a s)) := by
    have ht := original_J3_received_height P Prow hJ hr hR hfit a bounds s k
    exact inputHeight_mono hSource ⟨ht.1.le,ht.2.le⟩
  refine ⟨raw i0,raw i1,?_,background_public_height L bounds i1,?_,?_⟩
  · have he := public_constant_is_Bt hreg L
    change (backgroundPoly L hreg).coeff 0 = backgroundConstant hreg Prow a.1 at he
    rw [← he]
    exact background_public_height L bounds i0
  · intro v
    have he := rowAtOne_coeff_zero hreg L (Sum.inl v)
    change (rowAtOne L hreg (.inl v)).coeff 0 = pinConstant hreg Prow a.1 v at he
    rw [← he]
    exact row_at_one_public_height L bounds (.inl v) i0
  · intro v
    have he := rowAtOne_coeff_one hreg L a.2 rfl (Sum.inl v)
    change (rowAtOne L hreg (.inl v)).coeff 1 = pinDerivative hreg Prow a v at he
    rw [← he]
    exact row_at_one_public_height L bounds (.inl v) i1

#print axioms inputHeight_mono
#print axioms source_within_to_public
#print axioms row_at_one_public_height
#print axioms background_public_height
#print axioms original_J3_primitives_height

end
end J3R60
