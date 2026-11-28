import V8NativeMessageC3HermiteNative
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-! A sufficient explicit large-instance threshold for the actual
printed choices. There is no claim for arbitrarily retuned Q. -/
namespace V8NativeMessage.C3.Hermite.Native
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive
open V8PooledMenu.FiveCopy V8PooledRange
open RawMain Canonical
noncomputable section

theorem factorial_dyadic_valuation_le (n : ℕ) : padicValNat 2 n.factorial ≤ n := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p:=2) n
  rw [show (2:ℕ)-1=1 by decide,one_mul] at h
  exact h.trans_le (Nat.sub_le _ _)

theorem factorial_pair_dyadic_valuation_le (R Q : ℕ) :
    padicValInt 2 ((((R-1).factorial * Q.factorial):ℕ):ℤ) ≤ (R-1)+Q := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change padicValNat 2 ((R-1).factorial * Q.factorial) ≤ _
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  exact Nat.add_le_add (factorial_dyadic_valuation_le _) (factorial_dyadic_valuation_le _)

variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ]
  {G : Graph V E} {r : ThreePorts G} (F : FiveFile (Γ:=Γ) G r)

/-- The printed Q is the natural division in MAIN's parameter lemma.
Here n is the number of variables of the very same five-copy formula. -/
def mainLambda (V : Type) [Fintype V] := Nat.clog 2 (Fintype.card (Variable V))
def mainNu (V : Type) [Fintype V] := Nat.clog 2 (mainLambda V)
def sourceQ (V : Type) [Fintype V] := mainLambda V / (128*mainNu V)

theorem main_order_sub_one_le_directDegree : printedJ F-1 ≤ directDegree V E := by
  let d := directDegree V E
  let Q := F.layout.Q
  let R := F.layout.R
  have hQ : 0<Q := F.layout.positive_degree.trans F.layout.degree_lt_nodes
  have hR : R ≤ Q := F.layout.degree_lt_nodes.le
  change 1+d*R/Q-1≤d
  rw [Nat.add_comm 1,Nat.add_sub_cancel]
  calc
    d*R/Q ≤ d*Q/Q := Nat.div_le_div_right (Nat.mul_le_mul_left d hR)
    _ = d := Nat.mul_div_cancel _ hQ

theorem main_loss_le_three_degree_Q : ordinaryMainLoss F ≤ 3*directDegree V E*F.layout.Q := by
  let Q := F.layout.Q
  let d := directDegree V E
  have hval : padicValInt 2 ((δ F.layout:ℕ):ℤ) ≤ 2*Q := by
    refine (factorial_pair_dyadic_valuation_le F.layout.R Q).trans ?_
    have h := F.layout.degree_lt_nodes
    dsimp [Q] at *
    omega
  have hl : logLoss Q ≤ Q := Nat.log_le_self _ _
  change padicValInt 2 ((δ F.layout:ℕ):ℤ)*d + (printedJ F-1)*logLoss Q ≤ 3*d*Q
  calc
    _ ≤ 2*Q*d+d*Q :=
      Nat.add_le_add (Nat.mul_le_mul_right d hval)
        (Nat.mul_le_mul (main_order_sub_one_le_directDegree F) hl)
    _ = _ := by ring

theorem actual_degree_vs_wires (G₀ : Graph V E) (p₀ : ThreePorts G₀) :
    2*directDegree V E=wireSize V :=
  (source_register_dimensions G₀ p₀).1

theorem actual_variable_vs_root (G₀ : Graph V E) (p₀ : ThreePorts G₀) :
    Fintype.card (Variable V)≤rootSize V := by
  have h := (source_register_dimensions G₀ p₀).2.1
  change _≤25*Fintype.card V/2+3
  omega

theorem source_Q_le (hprinted : F.layout.Q=sourceQ V) :
    F.layout.Q ≤ 1024*(rootU V+1) := by
  let c := Nat.clog 2 (rootSize V)
  let u := rootU V
  let lam := mainLambda V
  let nu := mainNu V
  let Q := F.layout.Q
  have hQ : 0<Q := F.layout.positive_degree.trans F.layout.degree_lt_nodes
  have hformula : Q=lam/(128*nu) := hprinted
  have hNu : 0<nu := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, Nat.mul_zero, Nat.div_zero] at hformula
    omega
  have hLam : lam≤c := Nat.clog_mono_right _ (actual_variable_vs_root G r)
  have hquo : (128*nu)*Q≤lam := by
    rw [hformula,mul_comm]
    exact Nat.div_mul_le_self _ _
  have hbase : 128≤128*nu := by
    simpa only [Nat.mul_one] using (Nat.mul_le_mul_left 128 (Nat.succ_le_of_lt hNu))
  have h128 : 128*Q≤lam := (Nat.mul_le_mul_right Q hbase).trans hquo
  have hu : u=c/131072 := rfl
  have hmod : c%131072<131072 := Nat.mod_lt _ (by decide)
  have hdecomp : c%131072+131072*u=c := by rw [hu,Nat.mod_add_div]
  change Q≤1024*(u+1)
  omega

theorem exponential_reserve (u : ℕ) (hu : 15≤u) : 256*u*(u+1)≤2^(u+1) := by
  induction u,hu using Nat.le_induction with
  | base => decide
  | succ u hu ih =>
    have hs : u+2≤2*u := by omega
    calc
      256*(u+1)*(u+1+1) ≤ 256*(u+1)*(2*u) := Nat.mul_le_mul_left _ hs
      _ = (256*u*(u+1))*2 := by ring
      _ ≤ 2^(u+1)*2 := Nat.mul_le_mul_right 2 ih
      _ = 2^(u+1+1) := (pow_succ 2 (u+1)).symm

theorem sufficient_printed_reserve (hprinted : F.layout.Q=sourceQ V)
    (hlarge : 15≤rootU V) (hM : rootU V≤wireSize V) (t : Site V) :
    ordinaryMainLoss F ≤ 2*(printedH V*nodeD t) := by
  let d := directDegree V E
  let Q := F.layout.Q
  let m := wireSize V
  let u := rootU V
  let H := printedH V
  let D := nodeD t
  have hp : 0<u := (show 0<15 by decide).trans_le hlarge
  have hQ : Q≤1024*(u+1) := source_Q_le F hprinted
  have hd : 2*d=m := actual_degree_vs_wires G r
  have hH : 3*m≤H*u := (J6ActiveSchedule.height_bounds m u hp hM).1
  have hD : 2^(u+1)≤D := native_node_reserve_lower hp hM t
  have hE : 256*u*(u+1)≤2^(u+1) := exponential_reserve u hlarge
  change ordinaryMainLoss F ≤ 2*(H*D)
  calc
    _ ≤ 3*d*Q := main_loss_le_three_degree_Q F
    _ ≤ 3*d*(1024*(u+1)) := Nat.mul_le_mul_left _ hQ
    _ = 512*3*(2*d)*(u+1) := by ring
    _ = 512*(3*m)*(u+1) := by rw [hd]; ring
    _ ≤ 512*(H*u)*(u+1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hH)
    _ = 2*(H*(256*u*(u+1))) := by ring
    _ ≤ 2*(H*D) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hE.trans hD))

theorem ordinary_main_printed_margin (hprinted : F.layout.Q=sourceQ V)
    (hlarge : 15≤rootU V) (hM : rootU V≤wireSize V) (t : Site V) :
    ordinaryMainLoss F ≤ 2*(printedH V*nodeD t)+4*(wireSize V*(rootA V+1)) :=
  (sufficient_printed_reserve F hprinted hlarge hM t).trans (Nat.le_add_right _ _)

#print axioms factorial_dyadic_valuation_le
#print axioms factorial_pair_dyadic_valuation_le
#print axioms main_order_sub_one_le_directDegree
#print axioms main_loss_le_three_degree_Q
#print axioms actual_degree_vs_wires
#print axioms actual_variable_vs_root
#print axioms source_Q_le
#print axioms exponential_reserve
#print axioms sufficient_printed_reserve
#print axioms ordinary_main_printed_margin
end
end V8NativeMessage.C3.Hermite.Native
