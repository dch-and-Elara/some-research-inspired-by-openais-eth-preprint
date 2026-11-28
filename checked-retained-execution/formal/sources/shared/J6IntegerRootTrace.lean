import J6IntegerPowerCost

/-! Every actual threshold candidate of the greedy bit decoder is bounded
by the declared word size; the candidate cost is not an oracle count. -/
namespace J6IntegerRootTrace

def probes (f : ℕ → ℕ) (a : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | b+1, l =>
    let k := l+2^b
    k :: probes f a b (if f k ≤ a then k else l)

theorem length_matches (f : ℕ → ℕ) (a b l : ℕ) :
    (probes f a b l).length = (J6IntegerRoot.recoverNat f a b l).2 := by
  rw [J6IntegerRoot.recoverNat_steps]
  induction b generalizing l with
  | zero => rfl
  | succ b ih => simp only [probes,List.length_cons,ih]

theorem probe_bounds (f : ℕ → ℕ) (a b l : ℕ) (x : ℕ) (hm : x ∈ probes f a b l) :
    l ≤ x ∧ x < l+2^b := by
  induction b generalizing l with
  | zero => simp [probes] at hm
  | succ b ih =>
    let k := l+2^b
    have h' : x = k ∨ x ∈ probes f a b (if f k ≤ a then k else l) :=
      List.mem_cons.mp hm
    have hpos : 0 < (2:ℕ)^b := by positivity
    rw [pow_succ]
    rcases h' with h'|h'
    · subst x
      dsimp [k]
      omega
    · by_cases q : f k ≤ a
      · rw [if_pos q] at h'
        obtain ⟨hlo,hhi⟩ := ih k h'
        dsimp [k] at hlo hhi
        omega
      · rw [if_neg q] at h'
        obtain ⟨hlo,hhi⟩ := ih l h'
        omega

theorem actual_width_and_budget (a b e : ℕ) :
    (∀ x ∈ probes (fun y => y^e) a b 0,
        ∀ i ≤ e, (J6IntegerPowerCost.countedPower x i).1 < 2^(1+(e+1)*b)) ∧
    ((probes (fun y => y^e) a b 0).map (fun _ =>
        8*e*(1+(e+1)*b)^2+4*(1+(e+1)*b))).sum ≤ 12*(b+1)^3*(e+1)^3 := by
  constructor
  · intro x hx i hi
    have h := (probe_bounds _ _ _ _ _ hx).2
    have hw := J6IntegerPowerCost.power_width_uniform b x e i (by simpa using h) hi
    have hb : 1+e*b ≤ 1+(e+1)*b := by gcongr; omega
    exact hw.trans_le (Nat.pow_le_pow_right (by decide) hb)
  · rw [List.map_const',List.sum_replicate,length_matches,J6IntegerRoot.recoverNat_steps]
    exact J6IntegerPowerCost.charge_poly b e

#print axioms length_matches
#print axioms probe_bounds
#print axioms actual_width_and_budget
end J6IntegerRootTrace