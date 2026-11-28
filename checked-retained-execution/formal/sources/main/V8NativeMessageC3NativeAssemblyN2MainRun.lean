import V8NativeMessageC3NativeAssemblyN2MainCore

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1050000

/-! Entire completed first/second-pass admission at one fixed tuple.
The result is a cost certificate for the source's explicit loop, not a
lower bound on obtaining the same value by a different algorithm. -/
namespace V8NativeMessage.C3.NativeAssembly.MainScan
open scoped Classical BigOperators
noncomputable section
variable {V G R : Type*} [Fintype V] [Fintype G] [CommSemiring R]

def acceptedRun (L : Frame V G) (A : G→(V→Bool)→R) : Meter R :=
  if h : feasible L then
    (∑ g, (secondScan L A h g).1,
     ∑ g, (secondScan L A h g).2.1,
     ∏ g, (secondScan L A h g).2.2)
  else (0,0,0)

omit [Fintype G] in theorem feasible_iff_unrestricted (L : Frame V G) :
    feasible L ↔ ∀g, ∃ x, unrestricted L g x :=
  forall_congr' (representative_exists_iff L)

theorem skip_infeasible (L : Frame V G) (A : G→(V→Bool)→R)
    (hv : ∃g, ¬∃ x, unrestricted L g x) :
    acceptedRun L A=(0,0,0) := by
  apply dif_neg
  intro h
  obtain ⟨g,hg⟩ := hv
  exact hg ((feasible_iff_unrestricted L).mp h g)

theorem accepted_test_count (L : Frame V G) (A : G→(V→Bool)→R) (h : feasible L) :
    (acceptedRun L A).1=∑ g : G, 2^Fintype.card {v : V // L.group v=g} := by
  rw [acceptedRun,dif_pos h]
  exact Finset.sum_congr rfl (fun g _ => second_tests_every_word L A h g)

theorem accepted_tuple_value (L : Frame V G) (A : G→(V→Bool)→R) (h : feasible L) :
    (acceptedRun L A).2.2 =
      ∏ g : G, ∑ x ∈ (Finset.univ : Finset (Word L g)).filter (eligible L g),
        A g (merge L (repWord L h) g x) := by
  rw [acceptedRun,dif_pos h]
  exact Finset.prod_congr rfl (fun g _ => second_value_is_actual_fibre L A h g)

omit [CommSemiring R] in
theorem sum_groupSize (L : Frame V G) :
    (∑ g : G, Fintype.card {v : V // L.group v=g})=Fintype.card V := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv L.group)
  simpa only [Fintype.card_sigma] using h

omit [CommSemiring R] in
theorem largest_group_size (L : Frame V G) [Nonempty G] :
    ∃ g : G, (∀ a, Fintype.card {v : V // L.group v=a} ≤ Fintype.card {v : V // L.group v=g}) ∧
      Fintype.card V ≤ Fintype.card G * Fintype.card {v : V // L.group v=g} := by
  let m (g : G) := Fintype.card {v : V // L.group v=g}
  obtain ⟨g,_,hg⟩ := Finset.exists_max_image Finset.univ m Finset.univ_nonempty
  have hgm : ∀ a : G, m a≤m g := fun a => hg a (Finset.mem_univ a)
  refine ⟨g,hgm,?_⟩
  change Fintype.card V≤Fintype.card G*m g
  rw [←sum_groupSize L]
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    (Finset.sum_le_sum (fun a _ => hgm a) : (∑ a : G,m a)≤∑ _a : G,m g)

theorem accepted_run_exponent (L : Frame V G) [Nonempty G] (A : G→(V→Bool)→R) (h : feasible L) :
    (2:ℕ)^Fintype.card V ≤ ((acceptedRun L A).1)^Fintype.card G := by
  obtain ⟨g,_,hmax⟩ := largest_group_size L
  let m := Fintype.card {v : V // L.group v=g}
  have ht : (2:ℕ)^m ≤ (acceptedRun L A).1 := by
    rw [accepted_test_count L A h]
    exact Finset.single_le_sum (f:=fun a : G => (2:ℕ)^Fintype.card {v : V // L.group v=a})
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  calc
    _ ≤ (2:ℕ)^(Fintype.card G*m) := Nat.pow_le_pow_right (by decide) hmax
    _ = ((2:ℕ)^m)^Fintype.card G := by rw [Nat.mul_comm (Fintype.card G),pow_mul]
    _ ≤ _ := Nat.pow_le_pow_left ht _

#print axioms feasible_iff_unrestricted
#print axioms skip_infeasible
#print axioms accepted_test_count
#print axioms accepted_tuple_value
#print axioms sum_groupSize
#print axioms largest_group_size
#print axioms accepted_run_exponent
end
end V8NativeMessage.C3.NativeAssembly.MainScan
