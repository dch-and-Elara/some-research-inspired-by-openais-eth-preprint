import V8NativeMessageN7Kernel

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

/-! The zero-mode really is the partial Boolean shift at parity. The
surviving coefficient is proved to be the image of an odd/odd base
ratio, hence 1 in any characteristic-two receiving extension. -/
namespace V8NativeMessage.N7
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid P1DyadicGridBridge J6R9PacketCoeff
open P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open J6R9PacketChild J6R9PacketTiles J6R10RowAffine J6R10PacketAssembly J6R9PacketLocal J6R11Blueprint

noncomputable section

section Coeff
variable {S : Type*} [CommRing S]

private theorem odd_cast_one (h₂ : (2:S)=0) {u : ℤ} (hu : Odd u) : (u:S)=1 := by
  obtain ⟨v,rfl⟩ := hu
  simp [h₂]

theorem rho_mod_two (ψ : TwoLocal→+*S) (h₂ : (2:S)=0) {a : ℕ} {t : ℤ}
    (mem : t∈grid a) : ψ (rho a t)=1 := by
  obtain ⟨k,s,r,hs,hr,hT,h0⟩ := cauchy_derivative_common_content mem
  have e : rho a t*(r:TwoLocal)=(s:TwoLocal) := by
    apply twoLocalRat_injective
    rw [map_mul,map_intCast,map_intCast,rho_rat mem]
    unfold derivRatio
    rw [hT,h0,Int.cast_mul,Int.cast_mul,cast_pow₂]
    have hr' : (r:ℚ)≠0 := by exact_mod_cast odd_int_ne_zero hr
    have hp : (2:ℚ)^k≠0 := pow_ne_zero _ (by decide)
    field_simp
  have H := congrArg ψ e
  rw [map_mul,map_intCast,map_intCast,odd_cast_one h₂ hr,odd_cast_one h₂ hs,mul_one] at H
  exact H

theorem normalized_at_zero (ψ : TwoLocal→+*S) (a : ℕ) (t k : ℤ) :
    (V8PooledMenu.normalizedW a t k).eval₂ ψ 0 = if k=t then ψ (rho a t) else 0 := by
  classical
  by_cases h : k=t
  · rw [V8PooledMenu.normalizedW,if_pos h,if_pos h,Polynomial.eval₂_mul,Polynomial.eval₂_C]
    simp [V8PooledMenu.normalizedFactors,Polynomial.eval₂_finset_prod,Polynomial.eval₂_add,
      Polynomial.eval₂_mul]
  · simp [V8PooledMenu.normalizedW,h,Polynomial.eval₂_mul]

theorem normalized_shift_parity (ψ : TwoLocal→+*S) (h₂ : (2:S)=0)
    {a : ℕ} {t : ℤ} (mem : t∈grid a) (k : ℤ) (z : S) :
    (V8PooledMenu.normalizedW a t k).eval₂ ψ (2*z) = if k=t then 1 else 0 := by
  rw [h₂,zero_mul,normalized_at_zero,rho_mod_two ψ h₂ mem]

end Coeff

section Actual
variable {E A B G S : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] [CommRing S] {a : ℕ} {N : Network E A B} {f : ℤ[X]}

omit [Fintype E] [Fintype A] [Fintype B] [CommRing S] in
theorem shifted_col_unique (P : PhysicalPacking N a G) (w : Physical a P.copies G)
    {t : ℤ} (x y : E) (px : (P.seat x).1=w.1) (py : (P.seat y).1=w.1)
    (dx : ((P.seat x).2.val:ℤ)-(w.2.val:ℤ)=t)
    (dy : ((P.seat y).2.val:ℤ)-(w.2.val:ℤ)=t) : x=y := by
  apply P.seat.injective
  refine Prod.ext (px.trans py.symm) (Fin.ext ?_)
  have eq : ((P.seat x).2.val : ℤ) = (P.seat y).2.val := by omega
  exact_mod_cast eq

def shiftBit (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
    (w : Physical a P.copies G)
    (X : ColBits (fun e => P.seat e) P.mask i (rowGroup P.mask i w)) : S :=
  ∑ q : {q : E // colGroup P.mask i (P.seat q)=rowGroup P.mask i w},
    if (P.seat q.val).1=w.1 ∧ ((P.seat q.val).2.val:ℤ)-(w.2.val:ℤ)=t then
      bit S (X q) else 0

omit [Fintype A] [Fintype B] in
theorem local_shift_parity (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (mem : t∈grid a) (w : Physical a P.copies G)
    (X : ColBits (fun e => P.seat e) P.mask i (rowGroup P.mask i w))
    (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (ψ : Residue f 1 p→+*S) (charTwo : (2:S)=0) :
    ψ (localValue (fun e => P.seat e) P.mask i t p h₂ z w X)=shiftBit P i t w X := by
  let ev := eval₂RingHom (ψ.comp (J6ZeroTransport.reduceAt p h₂)) (2*ψ z)
  rw [← V8PooledMenu.localScaled_eval P i t w X p h₂ z ψ]
  change ev (V8PooledMenu.localScaled P i t w X)=_
  rw [V8PooledMenu.localScaled,map_sum,shiftBit]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : (P.seat q.val).1=w.1
  · simp only [if_pos hp,map_mul]
    change (V8PooledMenu.normalizedW a t _).eval₂ _ _ *
        ev (C (bit TwoLocal (X q)))=_
    rw [normalized_shift_parity _ charTwo mem]
    by_cases hs : ((P.seat q.val).2.val:ℤ)-(w.2.val:ℤ)=t
    · have ha : (P.seat q.val).1=w.1 ∧ ((P.seat q.val).2.val:ℤ)-(w.2.val:ℤ)=t := ⟨hp,hs⟩
      simp only [if_pos hs,if_pos ha,one_mul]
      cases X q <;> simp [ev,bit]
    · have hn : ¬((P.seat q.val).1=w.1 ∧ ((P.seat q.val).2.val:ℤ)-(w.2.val:ℤ)=t) := fun h=>hs h.2
      simp only [if_neg hs,if_neg hn,zero_mul]
  · have hn : ¬((P.seat q.val).1=w.1 ∧ ((P.seat q.val).2.val:ℤ)-(w.2.val:ℤ)=t) := fun h=>hp h.1
    simp only [if_neg hp,map_zero,if_neg hn]

def shiftBase (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (g : G)
    (v : PhysicalState P i g) (r : E) : S :=
  if h : rowGroup P.mask i (P.seat r)=g then
    shiftBit P i t (P.seat r) (fun q=>v.2 ⟨q.val,q.property.trans h⟩) else 0

omit [Fintype A] [Fintype B] in
theorem base_shift_parity (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (mem : t∈grid a) (g : G) (v : PhysicalState P i g) (r : E)
    (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (ψ : Residue f 1 p→+*S) (charTwo : (2:S)=0) :
    ψ (groupBase (fun e=>P.seat e) (fun e=>P.seat e) P.mask i t p h₂ z g v r)
      =shiftBase P i t g v r := by
  unfold groupBase shiftBase
  split
  · exact local_shift_parity P i mem _ _ p h₂ z ψ charTwo
  · exact map_zero ψ

theorem native_child_is_shift_at_parity (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (mem : t∈grid a)
    (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (file : EntryFile f 1 N) (hf : f.Monic) (g : G)
    (ψ : Residue f 1 p→+*S) (charTwo : (2:S)=0) :
    ψ (reduce p f 1 ((actualPacketHost P i ht hv p h₂ z file 0 g).contract hf))=
    ∑ v : PhysicalState P i g, ψ (oldState P i g p file hf v) *
      ∏ k, ∏ r ∈ actualRows (childBlock P i) g k,
        LiteralPortCompiler.affine
          (groupBit (fun e=>P.seat e) (fun e=>P.seat e) P.mask i g v r)
          (shiftBase P i t g v r) := by
  rw [actualPacketHost_receive P i ht hv p h₂ z file 0 g hf,map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul,map_prod]
  apply congrArg (ψ (oldState P i g p file hf v)*·)
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [actualPacket,V8PooledMenu.packet_map,J6R14ZeroMode.packet_constant]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [base_shift_parity P i mem g v r p h₂ z ψ charTwo]

end Actual

#print axioms rho_mod_two
#print axioms normalized_at_zero
#print axioms normalized_shift_parity
#print axioms shifted_col_unique
#print axioms local_shift_parity
#print axioms native_child_is_shift_at_parity
end
end V8NativeMessage.N7
