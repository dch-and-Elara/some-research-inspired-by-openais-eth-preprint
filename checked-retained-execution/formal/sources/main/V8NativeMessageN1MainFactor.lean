import V8NativeMessageN1MainRow

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

/-! Exact source N1 factor split and homogenized integer numerators.
The direct clause degree counts actual incidences, not a doubled
bound that charges unary pins as binary factors. -/
namespace V8NativeMessage.N1
open scoped Classical BigOperators Polynomial
open Polynomial V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}

def arity : Clause F→ℕ
  | .inl _ => 1
  | .inr _ => 2

theorem native_degree (hreg : ∀ v, GraphCutMoments.degree F v=3) :
    (∑ f : Clause F, arity f)=12*Fintype.card W := by
  have h : 3*Fintype.card W=2*F.card := by
    have h' := GraphCutMoments.sum_degree F
    simp_rw [hreg] at h'
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_comm] using h'
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [arity,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_coe,
    Clone,Fintype.card_prod,Fintype.card_fin]
  change Fintype.card W+(F.card*2+(Fintype.card W*4)*2)=12*Fintype.card W
  calc
    _ = Fintype.card W+2*F.card+8*Fintype.card W := by ring
    _ = _ := by omega

variable (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)

def clauseSet (g : Fin r) : Finset (Clause F) := Finset.univ.filter (fun f => L.factorGroup f=g)

def pins (g : Fin r) : Finset W := Finset.univ.filter (fun v => L.factorGroup (.inl v)=g)

def signedArg (x : Clone W→Bool) (s : W→Bool) (v : W) : Jet J :=
  signedLiteral (θ L x (.inl v) (v,0)) (s v)

def background (g : Fin r) (x : Clone W→Bool) : Jet J :=
  ∏ f : F ⊕ Clone W, if L.factorGroup (.inr f)=g then
    cloneFactor F hreg L (fun _ => false) x (.inr f) else 1

theorem native_factor_N1 (s : W→Bool) (g : Fin r) (x : Clone W→Bool) :
    nativeGroup F hreg L s g x =
      background L hreg g x * ∏ v ∈ pins L g, signedArg L x s v := by
  unfold nativeGroup pins background
  simp only [Finset.prod_filter]
  rw [Fintype.prod_sum_type,mul_comm]
  congr 1
  · apply Finset.prod_congr rfl
    intro f _
    cases f <;> rfl

variable {R BP : ℕ} (H : RowBound L hreg R BP)

def intLiteral (x : Clone W→Bool) (o : Occ F) (sgn : Bool) : ℤ[X] :=
  if sgn then iTheta L hreg H x o else C (δ R Q:ℤ)-iTheta L hreg H x o

def intFactor (s : W→Bool) (x : Clone W→Bool) : Clause F→ℤ[X]
  | .inl v => intLiteral L hreg H x (.inl v) (s v)
  | .inr (.inl e) => C (δ R Q:ℤ)^2 -
      intLiteral L hreg H x (.inr (.inl (e,true))) false *
      intLiteral L hreg H x (.inr (.inl (e,false))) false
  | .inr (.inr i) => C (δ R Q:ℤ)^2 -
      intLiteral L hreg H x (.inr (.inr (i,true))) true *
      intLiteral L hreg H x (.inr (.inr (i,false))) false

def jetify (J : ℕ) : ℤ[X]→+*Jet J := (AdjoinRoot.mk _).comp intToRat

theorem jetify_C_nat (J a : ℕ) : jetify J (C (a:ℤ))=(a:Jet J) := by
  unfold jetify
  rw [RingHom.comp_apply]
  change (AdjoinRoot.mk _) ((C (a:ℤ)).map (Int.castRingHom ℚ))=_
  simp

theorem jetify_iTheta (x : Clone W→Bool) (o : Occ F) :
    jetify J (iTheta L hreg H x o) =
      (δ R Q:Jet J)*θ L x (occClause o) (occVar hreg o) := by
  unfold jetify
  rw [RingHom.comp_apply,map_iTheta,map_mul,thetaPoly_mk]
  simp

theorem jetify_literal (x : Clone W→Bool) (o : Occ F) (sgn : Bool) :
    jetify J (intLiteral L hreg H x o sgn) =
      (δ R Q:Jet J)*signedLiteral (θ L x (occClause o) (occVar hreg o)) sgn := by
  cases sgn
  · simp only [intLiteral,signedLiteral,Bool.false_eq_true,if_false,map_sub,jetify_C_nat,jetify_iTheta]
    ring
  · simp only [intLiteral,signedLiteral,if_true,jetify_iTheta]

theorem jetify_factor (x : Clone W→Bool) (s : W→Bool) (f : Clause F) :
    jetify J (intFactor L hreg H s x f)=(δ R Q:Jet J)^(arity f)*cloneFactor F hreg L s x f := by
  rcases f with v | e | ⟨v,j⟩
  · simpa only [intFactor,arity,occClause,occVar,pow_one,cloneFactor] using
      jetify_literal L hreg H x (.inl v) (s v)
  · simp only [intFactor,arity,occClause,occVar,cloneFactor,Bool.false_eq_true,if_false,if_true,
      map_sub,map_pow,map_mul,jetify_C_nat,jetify_literal,signedLiteral]
    ring
  · simp only [intFactor,arity,occClause,occVar,cloneFactor,Bool.false_eq_true,if_false,if_true,
      map_sub,map_pow,map_mul,jetify_C_nat,jetify_literal,signedLiteral]
    ring

theorem norm_literal (x : Clone W→Bool) (o : Occ F) (sgn : Bool) :
    coeffNorm (intLiteral L hreg H x o sgn)≤B₀ W R Q BP := by
  cases sgn
  · simp only [intLiteral,Bool.false_eq_true,if_false]
    have h := norm_sub (C (δ R Q:ℤ)) (iTheta L hreg H x o)
    rw [norm_C,Int.natAbs_natCast] at h
    exact h.trans (Nat.add_le_add_left (norm_iTheta L hreg H x o) _)
  · simp only [intLiteral,if_true]
    exact (norm_iTheta L hreg H x o).trans (Nat.le_add_left _ _)

def A (W : Type*) [Fintype W] (R Q BP : ℕ) : ℕ := 2*B₀ W R Q BP

omit [DecidableEq W] in
theorem δ_le_B₀ : δ R Q≤B₀ W R Q BP := Nat.le_add_right _ _

omit [DecidableEq W] in
theorem norm_binary (p q : ℤ[X]) (hp : coeffNorm p≤B₀ W R Q BP)
    (hq : coeffNorm q≤B₀ W R Q BP) :
    coeffNorm (C (δ R Q:ℤ)^2-p*q)≤A W R Q BP^2 := by
  let B := B₀ W R Q BP
  have h₁ : coeffNorm (C (δ R Q:ℤ)^2)≤B^2 := by
    apply (norm_pow _ _).trans
    rw [norm_C,Int.natAbs_natCast]
    exact Nat.pow_le_pow_left (δ_le_B₀ (W:=W) (R:=R) (Q:=Q) (BP:=BP)) _
  have h₂ : coeffNorm (p*q)≤B^2 := (norm_mul p q).trans (by
    rw [pow_two]; exact Nat.mul_le_mul hp hq)
  have h := (norm_sub (C (δ R Q:ℤ)^2) (p*q)).trans (Nat.add_le_add h₁ h₂)
  change _≤(2*B)^2
  rw [mul_pow]
  exact h.trans (by omega)

theorem norm_factor (x : Clone W→Bool) (s : W→Bool) (f : Clause F) :
    coeffNorm (intFactor L hreg H s x f)≤ A W R Q BP^(arity f) := by
  rcases f with v | e | i
  · simp only [intFactor,arity,pow_one]
    exact (norm_literal L hreg H x _ _).trans (by unfold A; omega)
  · simpa only [intFactor,arity] using norm_binary (W:=W) (R:=R) (Q:=Q) (BP:=BP)
      _ _ (norm_literal L hreg H x (.inr (.inl (e,true))) false)
      (norm_literal L hreg H x (.inr (.inl (e,false))) false)
  · simpa only [intFactor,arity] using norm_binary (W:=W) (R:=R) (Q:=Q) (BP:=BP)
      _ _ (norm_literal L hreg H x (.inr (.inr (i,true))) true)
      (norm_literal L hreg H x (.inr (.inr (i,false))) false)

#print axioms native_degree
#print axioms native_factor_N1
#print axioms jetify_iTheta
#print axioms jetify_literal
#print axioms jetify_factor
#print axioms norm_literal
#print axioms norm_binary
#print axioms norm_factor
end
end V8NativeMessage.N1
