import J6R11ProbeSetup

namespace J6R11Threshold
open scoped Classical Polynomial
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J1PPrinted

theorem printed_size_implies_numeric_guards (s C : ℕ) (hC : 0<C)
    (hsize : (2*epsDen)^30*C^10 ≤ Nat.clog 2 s) :
    0<Nat.clog 2 s ∧ C≤s ∧ 1≤J9PrintedSchedule.rootU (Nat.clog 2 s) := by
  have hbase : 0 < 2*epsDen := by decide
  have hC10 : C ≤ C^10 := by
    calc
      C = C^1 := (pow_one C).symm
      _ ≤ C^10 := Nat.pow_le_pow_right hC (by decide)
  have hCclog : C≤Nat.clog 2 s :=
    hC10.trans ((Nat.le_mul_of_pos_left _ (pow_pos hbase 30)).trans hsize)
  have htwo (n : ℕ) : n < (2:ℕ)^n := by
    induction n with
    | zero => decide
    | succ n hn => rw [pow_succ]; omega
  have hclogS : Nat.clog 2 s ≤ s :=
    (Nat.clog_le_iff_le_pow (by decide : 1<(2:ℕ))).mpr (Nat.le_of_lt (htwo s))
  have he0 : epsDen ≤ 2*epsDen := by omega
  have he1 : 2*epsDen ≤ (2*epsDen)^30 := by
    calc
      _ = (2*epsDen)^1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hbase (by decide)
  have heclog : epsDen ≤ Nat.clog 2 s := he0.trans (he1.trans
    ((Nat.le_mul_of_pos_right _ (pow_pos hC 10)).trans hsize))
  refine ⟨hC.trans_le hCclog,hCclog.trans hclogS,?_⟩
  change 1 ≤ Nat.clog 2 s / epsDen
  exact (Nat.le_div_iff_mul_le (by decide : 0<epsDen)).mpr (by simpa only [one_mul] using heclog)

#print axioms printed_size_implies_numeric_guards
end J6R11Threshold
