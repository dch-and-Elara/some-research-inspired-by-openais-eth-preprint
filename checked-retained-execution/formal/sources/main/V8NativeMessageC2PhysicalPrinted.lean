import V8NativeMessageC2PhysicalCut
import J1PPrintedMesh

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

/-! Discharge the finite collision margin at the actual C2 five-copy
root parameters. The freeze still supplies the published variance
receipt on its own labels, not independent resampling. -/
namespace V8NativeMessage.C2Physical
open scoped Classical BigOperators
open V8PooledRange V8PooledMenu.FiveCopy J1PPrinted
noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G}

omit [Fintype E] in
theorem printed_root_has_vertices (i : Fin (rootU V)) : 0<Fintype.card V := by
  by_contra hn
  have hn' : Fintype.card V=0 := by omega
  have hu := i.isLt
  simp only [rootU,rootSize,hn',Nat.mul_zero,Nat.zero_div,Nat.zero_add] at hu
  have hsmall : Nat.clog 2 3≤2 := (Nat.clog_le_iff_le_pow (by decide)).mpr (by decide)
  omega

omit [Fintype E] in
theorem original_size_lt_native_wires (V : Type) [Fintype V] : rootSize V<wireSize V := by
  unfold rootSize wireSize
  omega

omit [Fintype E] in
theorem printed_active_root (i : Fin (rootU V)) :
    J9PrintedSchedule.leafThreshold (rootSize V) (Nat.clog 2 (rootSize V))<wireSize V := by
  let s := rootSize V
  let l := Nat.clog 2 s
  have hu : 0<l/(128*1024) := Nat.zero_lt_of_lt i.isLt
  have hlogPos : 0<l := by omega
  have h1 : 1≤l.sqrt := Nat.le_sqrt.2 (by simpa using hlogPos)
  have hs : s≤s*l.sqrt := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left s h1
  have ht : (s+l.sqrt-1)/l.sqrt≤s := by
    apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul (show 0<l.sqrt by omega)).mpr
    rw [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul]
    omega
  exact ht.trans_lt (original_size_lt_native_wires V)

omit [Fintype E] in
theorem actual_printed_margin (i : Fin (rootU V)) : Margin V (sourceDelta (rootSize V)) := by
  have hU : 1≤J9PrintedSchedule.rootU (Nat.clog 2 (rootSize V)) := Nat.zero_lt_of_lt i.isLt
  have hp := (source_packing_conditions (rootSize V) (wireSize V) 0 hU (printed_active_root i)).1
  have ha : stepA (Nat.clog 2 (rootSize V)) 0=rootA V := by
    simp [stepA,stepU,epsDen,rootA,rootU]
  simpa only [Margin,cellCount_printed,stepD,ha] using hp

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The original C2 finite same-layout theorem with the actual
Delta = ceil(s_D^(9/10)) and the exact printed depth-zero schedule.
No extra numeric margin or positive population test is a premise. -/
theorem native_cut_source_parameters (P : Packing G p) (i : Fin (rootU V)) (γ : K)
    (hγ : 0≤γ) (hE : ExpansionOn G γ) (hloop : ∀ e, G e false≠G e true)
    (hv : VarianceOK P (sourceDelta (rootSize V))) :
    Nonempty (NativeCut P i γ) :=
  native_cut_exists P i γ hγ hE hloop (printed_root_has_vertices i) _
    hv (actual_printed_margin i)

#print axioms printed_root_has_vertices
#print axioms original_size_lt_native_wires
#print axioms printed_active_root
#print axioms actual_printed_margin
#print axioms native_cut_source_parameters
end
end V8NativeMessage.C2Physical
