import V8NativeMessageN4DLoss
import V8NativeMessageN4MainLoss
import V8NativeMessageC3HermitePrintedGuards

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6200000

/-! The finite common MAIN/D precision guard for the original four-copy
printed Q,R,J and D center. It holds at all actual nonzero centers,
including ±1, without a node-dependent unknown asymptotic threshold. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open Paper5.HybridClosure Paper5.D1Literal J6ActiveSchedule J6R9Recursive J1PPrinted V8PooledMenu
open V8NativeMessage.C3.Hermite V8NativeMessage.C3.Hermite.Native
noncomputable section

def mainLog (N : ℕ) : ℕ := Nat.clog 2 (4*N)
def mainLogLog (N : ℕ) : ℕ := Nat.clog 2 (mainLog N)
def mainPrintedQ (N : ℕ) : ℕ := mainLog N/(128*mainLogLog N)
def mainPrintedR (N β : ℕ) : ℕ := (β+3)*ceilSqrt (mainLog N)
def mainPrintedJ (N R Q : ℕ) : ℕ := 1+(12*N)*R/Q

theorem print_q_scale (N Q : ℕ) (hQ : 0<Q) (hq : Q=mainPrintedQ N) :
    128*Q≤mainLog N := by
  have hv : 0<mainLogLog N := by
    by_contra! h
    have h0 : mainLogLog N=0 := by omega
    unfold mainPrintedQ at hq
    rw [h0,mul_zero,Nat.div_zero] at hq
    omega
  have ha : 128≤128*mainLogLog N := by omega
  have hb : (128*mainLogLog N)*Q≤mainLog N := by
    rw [hq,mainPrintedQ,mul_comm]
    exact Nat.div_mul_le_self _ _
  exact (Nat.mul_le_mul_right Q ha).trans hb

theorem printed_J_prev (N R Q J : ℕ) (hQ : 0<Q) (hRQ : R≤Q) (hj : J=mainPrintedJ N R Q) :
    J-1≤12*N := by
  rw [hj,mainPrintedJ,Nat.add_comm 1,Nat.add_sub_cancel]
  calc
    _ ≤ (12*N)*Q/Q := Nat.div_le_div_right (Nat.mul_le_mul_left _ hRQ)
    _ = _ := Nat.mul_div_cancel _ hQ

theorem main_loss_at_printed_J (N R Q J : ℕ) (hQ : 0<Q) (hRQ : R≤Q)
    (hj : J=mainPrintedJ N R Q) : mainOrdinaryLoss N R Q J≤3*(12*N)*Q := by
  have hv : padicValInt 2 ((N1.δ R Q:ℕ):ℤ)≤2*Q := by
    unfold N1.δ
    exact (factorial_pair_dyadic_valuation_le R Q).trans (by omega)
  have hl : logLoss Q≤Q := Nat.log_le_self _ _
  change padicValInt 2 ((N1.δ R Q:ℕ):ℤ)*(12*N)+(J-1)*logLoss Q≤_
  calc
    _ ≤ 2*Q*(12*N)+(12*N)*Q := Nat.add_le_add (Nat.mul_le_mul_right _ hv)
      (Nat.mul_le_mul (printed_J_prev N R Q J hQ hRQ hj) hl)
    _ = _ := by ring

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
  {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}

theorem main_lambda_le_D (reg : ∀ v, GraphCutMoments.degree F v=3) :
    mainLog (Fintype.card W)≤Nat.clog 2 (oldRowSize F) := by
  have hs := oldRow_size_exact F reg
  exact Nat.clog_mono_right _ (by omega)

omit [DecidableEq W] in
theorem D_u_is_printed : widthU F=Nat.clog 2 (oldRowSize F)/(128*1024) := by
  simp [widthU,stepU,epsDen]

theorem Q_le_D_u (reg : ∀ v, GraphCutMoments.degree F v=3) (Q : ℕ) (hQ : 0<Q)
    (hq : Q=mainPrintedQ (Fintype.card W)) : Q≤1024*(widthU F+1) := by
  have h := (print_q_scale _ Q hQ hq).trans (main_lambda_le_D reg)
  rw [D_u_is_printed]
  omega

theorem original_guards_u_ge (reg : ∀ v, GraphCutMoments.degree F v=3) (R Q β : ℕ)
    (hQ : 0<Q) (hq : Q=mainPrintedQ (Fintype.card W)) (hβ : 1≤β)
    (hr : R=mainPrintedR (Fintype.card W) β) (h6 : 6*R≤Q) : 15≤widthU F := by
  let n := mainLog (Fintype.card W)
  let k := ceilSqrt n
  have he : 128*Q≤n := print_q_scale _ Q hQ hq
  have hs : n≤k*k := by simpa only [pow_two] using le_ceilSqrt_sq n
  have hk : 0<k := by
    by_contra! h
    have hh : k=0 := by omega
    rw [hh,Nat.zero_mul] at hs
    omega
  have hR4 : 4*k≤R := by
    rw [hr]
    exact Nat.mul_le_mul_right k (by omega)
  have h3072 : 3072*k≤n := by omega
  have hkGe : 3072≤k := Nat.le_of_mul_le_mul_right (h3072.trans hs) hk
  have hn : 15*(128*1024)≤n :=
    (show 15*(128*1024)≤3072*3072 by decide).trans
      ((Nat.mul_le_mul_left _ hkGe).trans h3072)
  rw [D_u_is_printed]
  exact (Nat.le_div_iff_mul_le (by decide)).mpr (hn.trans (main_lambda_le_D reg))

theorem literal_center_reserve (t : PublicCenter F reg f) :
    2^(widthU F+1)≤nodeScale t := by
  let u := widthU F
  let i := padicValInt 2 t.val
  have h₁ : 0<order (Fintype.card (DWire F)) u t.val := active_order_pos _ _ _ _ t.property
  have hi : i<u := by
    apply Nat.sub_pos_iff_lt.mp
    apply Nat.pos_of_ne_zero
    intro h
    change u-padicValInt 2 t.val=0 at h
    rw [order,h,mul_zero] at h₁
    exact (lt_irrefl _ h₁)
  have h₂ : i≤2*u := by omega
  change 2^(u+1)≤2^(2*u)/2^i
  rw [dyadic_div_pow h₂]
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem actual_four_main_reserve (d : LayoutReady F reg f) (t : PublicCenter F reg f)
    (R Q J β : ℕ) (hQ : 0<Q) (hq : Q=mainPrintedQ (Fintype.card W)) (hβ : 1≤β)
    (hr : R=mainPrintedR (Fintype.card W) β) (h6 : 6*R≤Q)
    (hj : J=mainPrintedJ (Fintype.card W) R Q) :
    mainOrdinaryLoss (Fintype.card W) R Q J≤2*height (24*Fintype.card W) (widthU F)*nodeScale t := by
  let n := Fintype.card W
  let M := 24*n
  let u := widthU F
  let h := height M u
  let D := nodeScale t
  have hRQ : R≤Q := by omega
  have hQ' : Q≤1024*(u+1) := Q_le_D_u reg Q hQ hq
  have hlarge : 15≤u := original_guards_u_ge reg R Q β hQ hq hβ hr h6
  obtain ⟨hu,huM⟩ := actual_height_guards d t
  have hh : 3*M≤h*u := (height_bounds M u hu huM).1
  have he : 256*u*(u+1)≤D := (exponential_reserve u hlarge).trans (literal_center_reserve t)
  change mainOrdinaryLoss n R Q J≤2*h*D
  calc
    _ ≤ 3*(12*n)*Q := main_loss_at_printed_J n R Q J hQ hRQ hj
    _ ≤ 3*(12*n)*(1024*(u+1)) := Nat.mul_le_mul_left _ hQ'
    _ = 512*(3*M)*(u+1) := by dsimp [M]; ring
    _ ≤ 512*(h*u)*(u+1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hh)
    _ = 2*h*(256*u*(u+1)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ he

#print axioms print_q_scale
#print axioms printed_J_prev
#print axioms main_loss_at_printed_J
#print axioms main_lambda_le_D
#print axioms Q_le_D_u
#print axioms original_guards_u_ge
#print axioms literal_center_reserve
#print axioms actual_four_main_reserve
end
end V8NativeMessage.N4
