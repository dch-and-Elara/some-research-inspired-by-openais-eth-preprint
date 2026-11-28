import V8NativeMessageN1MainHeight

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

/-! Bind the N1 rational bit-height ledger to actual intermediate states
of the N2 literal MAIN second pass, not arbitrary scalar callback results.
This is a width theorem; number of visited words/reads comes from N2. -/
namespace V8NativeMessage.N1
open scoped Classical BigOperators Polynomial
open V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}
variable (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
variable {R BP : ℕ} (H : RowBound L hreg R BP)

def scanPrefix (s : W→Bool) (h : feasible L.frame) (g : Fin r) (i : ℕ) : Jet J :=
  (fullFold (entry L.frame (nativeGroup F hreg L s) h g) ((words L.frame g).take i)).2.2

def eligiblePrefix (g : Fin r) (i : ℕ) : Finset (Word L.frame g) :=
  ((words L.frame g).take i).toFinset.filter (eligible L.frame g)

theorem exact_scan_prefix (s : W→Bool) (h : feasible L.frame) (g : Fin r) (i : ℕ) :
    scanPrefix L hreg s h g i=ratAccum L hreg s h g (eligiblePrefix L g i) := by
  let p := (words L.frame g).take i
  have hp : p.Nodup := (Finset.nodup_toList _).take
  unfold scanPrefix fullFold
  rw [foldl_accumulate,zero_add,← List.sum_toFinset _ hp]
  change ((AddMonoidHom.snd ℕ (Jet J)).comp (AddMonoidHom.snd ℕ (ℕ×Jet J)))
    (∑ x ∈ p.toFinset, entry L.frame (nativeGroup F hreg L s) h g x)=_
  rw [map_sum,ratAccum,eligiblePrefix,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : eligible L.frame g w <;> simp [entry,filled,hw]

include H in
theorem actual_prefix_rational_height (s : W→Bool) (h : feasible L.frame)
    (g : Fin r) (i : ℕ) (j : Fin J) :
    (jetCoeff J j (scanPrefix L hreg s h g i)).den∣(δ R Q)^(groupDeg L g) ∧
      (jetCoeff J j (scanPrefix L hreg s h g i)).num.natAbs≤2^room L g*A W R Q BP^(groupDeg L g) := by
  rw [exact_scan_prefix L hreg s h g i]
  exact accumulation_height L hreg H s h g (eligiblePrefix L g i) j

include H in
theorem actual_prefix_bit_height (s : W→Bool) (h : feasible L.frame)
    (g : Fin r) (i : ℕ) (j : Fin J) :
    within (room L g+(Nat.log 2 (A W R Q BP)+1)*groupDeg L g+1)
      (jetCoeff J j (scanPrefix L hreg s h g i)) := by
  obtain ⟨hd,hn⟩ := actual_prefix_rational_height L hreg H s h g i j
  exact bits_of_bounds (δ_pos R Q) (δ_le_base (W:=W))
    (Nat.lt_pow_succ_log_self (by decide) _).le hd hn

#print axioms exact_scan_prefix
#print axioms actual_prefix_rational_height
#print axioms actual_prefix_bit_height
end
end V8NativeMessage.N1
