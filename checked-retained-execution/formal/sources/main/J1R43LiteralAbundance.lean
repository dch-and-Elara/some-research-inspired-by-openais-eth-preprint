import J1R43LiteralMoments
import J1PhysicalPrinted
import MainProbe

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5900000
set_option linter.unusedSectionVars false

/-! Exact finite versions of the two final abundance exponents in J1.
The same tracked diagonal pins partition into actual ownership groups at
each node; the total lower bound does not identify distinct placements. -/
namespace J1R43Literal
open scoped BigOperators
open DiagonalAbundance MainProbe

theorem from_reserved_card_floor (N H r K k : ℕ)
    (hN : 12≤N) (hH : N≤4*H+6) (hr : 0<r) (hK : 0<K)
    (hk : ((H:ℚ)/(2*(r:ℚ)*(K:ℚ))) < k) :
    ((N:ℚ)/(16*(r:ℚ)*(K:ℚ))) < k := by
  have h8 : N≤8*H := by omega
  have h8q : (N:ℚ)≤8*(H:ℚ) := by exact_mod_cast h8
  have hrq : (0:ℚ)<r := by exact_mod_cast hr
  have hKq : (0:ℚ)<K := by exact_mod_cast hK
  calc
    _ = ((N:ℚ)/8)/(2*(r:ℚ)*(K:ℚ)) := by field_simp; ring
    _ ≤ (H:ℚ)/(2*(r:ℚ)*(K:ℚ)) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ < _ := hk

theorem printed_K_power (N : ℕ) (hN : 0<N) :
    (J1PhysicalPrinted.sourceR (Nat.clog 2 (4*N)) ^
      J1PhysicalPrinted.sourceQ (Nat.clog 2 (4*N)))^256 ≤ 8*N := by
  apply (J1PhysicalPrinted.source_packing _).trans
  let L := Nat.clog 2 (4*N)
  have ho : 1<4*N := by omega
  have hp : 2^(L-1)<4*N := Nat.pow_pred_clog_lt_self (by decide) ho
  have hl : 0<L := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by simpa using ho)
  change 2^L≤8*N
  calc
    _ = 2^(L-1)*2 := by rw [← pow_succ,Nat.sub_add_cancel hl]
    _ ≤ (4*N)*2 := Nat.mul_le_mul_right _ hp.le
    _ = _ := by ring

theorem finite_power_floor (N r K k : ℕ) (hN : 0<N) (hr : 0<r) (hK : 0<K)
    (hp : K^256≤8*N) (hk : ((N:ℚ)/(16*(r:ℚ)*(K:ℚ))) < k) :
    N^255 < 8*(16*r*k)^256 := by
  have hrq : (0:ℚ)<r := by exact_mod_cast hr
  have hKq : (0:ℚ)<K := by exact_mod_cast hK
  have hn := (div_lt_iff₀ (show (0:ℚ)<16*(r:ℚ)*(K:ℚ) by positivity)).mp hk
  have hn' : (N:ℚ)<16*(r:ℚ)*(k:ℚ)*(K:ℚ) := by nlinarith only [hn]
  have hNat : N<16*r*k*K := by exact_mod_cast hn'
  have hpow : N^256<(16*r*k*K)^256 := Nat.pow_lt_pow_left hNat (by decide)
  rw [mul_pow] at hpow
  have hfinal := hpow.trans_le (Nat.mul_le_mul_left ((16*r*k)^256) hp)
  apply (Nat.mul_lt_mul_left hN).mp
  calc
    N*N^255 = N^256 := by rw [mul_comm]; exact (pow_succ N 255).symm
    _ < (16*r*k)^256*(8*N) := hfinal
    _ = _ := by ring

section Actual
variable {I S X C A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A]

theorem owned_partition (D : DiagonalLayout I S X C A) (i : I) :
    (∑ g : S,(ownedPins D i g Finset.univ).card)=Fintype.card A := by
  unfold ownedPins
  simpa using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset A)
    (Finset.univ : Finset S) (fun a => (D.slot a).2 i)

theorem sum_owned_floor (D : DiagonalLayout I S X C A) (i : I) (N K : ℕ) (hK : 0<K)
    (hg : ∀ g, ((N:ℚ)/(16*(Fintype.card S:ℚ)*(K:ℚ))) <
        ((ownedPins D i g Finset.univ).card:ℚ)) :
    ((N:ℚ)/(16*(K:ℚ))) < (Fintype.card A:ℚ) := by
  let x := ((N:ℚ)/(16*(Fintype.card S:ℚ)*(K:ℚ)))
  have hs : (∑ g : S,x) < ∑ g : S,((ownedPins D i g Finset.univ).card:ℚ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun g _ => hg g)
  rw [← Nat.cast_sum,owned_partition D i] at hs
  have he : (∑ g : S,x)=(N:ℚ)/(16*(K:ℚ)) := by
    have hrq : (0:ℚ)<Fintype.card S := by
      exact_mod_cast (Fintype.card_pos : 0<Fintype.card S)
    have hKq : (0:ℚ)<K := by exact_mod_cast hK
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    unfold x
    field_simp
  rwa [he] at hs

end Actual

#print axioms from_reserved_card_floor
#print axioms printed_K_power
#print axioms finite_power_floor
#print axioms owned_partition
#print axioms sum_owned_floor

end J1R43Literal