import J6R12RepackRootChoice
import J6R11RepackRootBalance
import J6R10ReachablePrinted

/-! Exact printed numerical schedule at the J6 root, before any
asymptotic size estimate or bit-cost argument. -/
namespace J6R12Repack
open scoped Polynomial BigOperators
open J6Mesh J1PPrinted J6ActiveRun J6R10Reachable J6R11Repack J6R10Repack J6R11Blueprint
open P11FullPacking J6OrientedHost
variable {S V : Type} [LinearOrder S] [Fintype S] [Fintype V]

theorem mesh_root_width (m native : ℕ) (hn : native≤m) :
    stepU (Nat.clog 2 (physicalSize m native)) 0 = u m := by
  rw [(physicalSize_ceiling m native hn).2.2]
  unfold stepU epsDen lambda u
  simp only [pow_zero,mul_one]
  omega

theorem mesh_root_bits (m native : ℕ) (hn : native≤m) :
    stepA (Nat.clog 2 (physicalSize m native)) 0 = a m := by
  simp only [stepA,zero_add,Finset.range_one,Finset.sum_singleton,mesh_root_width m native hn]
  unfold u a
  omega

theorem mesh_root_linear_bound (m native : ℕ) (hn : native≤m) :
    M m ≤ 2*physicalSize m native := by
  have hb : 1≤lambda m := by unfold lambda; have := b_pos m; omega
  have he : lambda m - 1 + 1 = lambda m := by omega
  have hM : M m = 2^(lambda m-1)*2 := by
    unfold M
    rw [← pow_succ,he]
  rw [hM]
  have h := (physicalSize_ceiling m native hn).1
  omega

theorem printed_cutoff_exact (s lam : ℕ) (hd : 0 < lam.sqrt) :
    J9PrintedSchedule.leafThreshold s lam = J6R9ZeroCutoff.cutoff s lam := by
  let d := lam.sqrt
  let q := (s+d-1)/d
  let x := (s:ℚ)/d
  change q = ⌈x⌉₊
  have hd' : 0 < (d:ℚ) := by exact_mod_cast hd
  have hq : s≤q*d := J9PrintedSchedule.le_roundup_mul s d hd
  have hceil : s≤⌈x⌉₊ * d := by
    have h := (div_le_iff₀ hd').mp (Nat.le_ceil x)
    exact_mod_cast h
  apply le_antisymm
  · apply Nat.le_of_lt_succ
    change (s+d-1)/d < ⌈x⌉₊+1
    have hd0 : 0 < d := hd
    apply (Nat.div_lt_iff_lt_mul hd0).mpr
    rw [Nat.add_mul,one_mul]
    omega
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hd').mpr
    exact_mod_cast hq

/-- Both the root's bit width and the active-call test are measured at the
same actual input size; no guessed data sizes enter this statement. -/
theorem actual_printed_root_ready_size (f : ℤ[X]) (ell p m l q native : ℕ)
    (T : Plant V m q) (w : Fin (a m) → S)
    (mask : MaskFamily (a m) (K m) S) (hm : m≤K m) (hL : 2*l=L m)
    (hS : Fintype.card S=64) (hn : native≤m) (g : S) :
    let c := physicalRootCall f ell p m l q T w
    let s := physicalSize m native
    let shape := printedShape (Host:=PhysicalHost f ell) (Mode:=Unit) s (fun _ _ _ => 0)
    shape.levelWidth c.depth=u m ∧ shape.levelBits c.depth=a m ∧
    shape.cutoff < c.edges ∧ c.edges ≤ 2*s := by
  have hpos : 0 < (Nat.clog 2 (physicalSize m native)).sqrt := by
    rw [(physicalSize_ceiling m native hn).2.2]
    apply Nat.sqrt_pos.mpr
    unfold lambda
    have := b_pos m
    omega
  refine ⟨mesh_root_width m native hn,mesh_root_bits m native hn,?_,mesh_root_linear_bound m native hn⟩
  change J9PrintedSchedule.leafThreshold (physicalSize m native) (Nat.clog 2 (physicalSize m native)) < M m
  rw [printed_cutoff_exact _ _ hpos]
  let P := rootPacking m l q T w mask hm hL hS
  let n := Nat.card (ChildEdge (rootNetwork T w)
    (J6R10Repack.atGroup P (J6RepairedCentered.coord m)) g)
  have hcut : J6R9ZeroCutoff.cutoff (physicalSize m native) (Nat.clog 2 (physicalSize m native)) < n :=
    actual_repacked_root_children_active m l q native T w mask hm hL hS hn g
  have hm' : 32*n=M m := actual_repacked_root_group_size m l q T w mask hm hL hS g
  omega

#print axioms mesh_root_width
#print axioms mesh_root_bits
#print axioms mesh_root_linear_bound
#print axioms printed_cutoff_exact
#print axioms actual_printed_root_ready_size
end J6R12Repack
