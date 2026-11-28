import J6R16ModeCostSite
import J6R27PrescribedProbeRoot
import J6R32RootGeneratedRegistryInputsSite

/-! The exact R16 inherited precision and depth invariant is initialized
after the true prescribed exterior step, without equating its field
word or host with any native-prefix slot's value. -/
namespace J6R68AbsolutePrescribed
open scoped Polynomial
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R14ZeroMode J6R16ModeCost J6R24MeteredRecursion J6R9Recursive
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6Mesh J6OrientedHost J6R11Repack J6R24LegalLayout J6R30GeneratedRootLayout J6R31RootResidentTables

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 23000000
set_option maxRecDepth 4200
set_option quotPrecheck false

structure AbsoluteSeed {f : ℤ[X]} {ell : ℕ} (s C : ℕ) (call : Call (PhysicalHost f ell)) : Prop where
  stable : Stable s C call
  depth : call.depth ≤ pathLimit s C
  prec : call.prec ≤ inputPrecisionCap s C call.depth

theorem true_depth_zero_seed {f : ℤ[X]} {ell s C : ℕ} {r : Call (PhysicalHost f ell)}
    (h : Stable s C r) (d0 : r.depth=0) (p0 : r.prec ≤ C*s) : AbsoluteSeed s C r := by
  refine ⟨h,by simp only [d0,Nat.zero_le],?_⟩
  simpa [inputPrecisionCap,d0] using p0

section Schedule
variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {r c : Call (PhysicalHost f ell)}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
include cfg

theorem absolute_register_fits_next
    (hs : Stable s C c) (hc : c.prec ≤ inputPrecisionCap s C c.depth)
    (active : (SP).cutoff<c.edges) (t : Center SP c) :
    registerPrecision SP c t ≤ inputPrecisionCap s C (c.depth+1) := by
  let lam := Nat.clog 2 s
  let a := stepA lam c.depth
  let b := 40*C*s*(lam+1)
  have ha : J9PrintedSchedule.leafThreshold s lam<c.edges := active
  obtain ⟨hu,_,hUM⟩ :=
    printed_taper_legal s c.edges C c.depth cfg.widthPos cfg.constPos cfg.size ha hs.sizeByDepth
  have hM : c.edges ≤ C*s := (Nat.le_mul_of_pos_left _ (by positivity : 0<(8:ℕ)^c.depth)).trans
    hs.sizeByDepth
  have hm := precision_increment_bound lam c.depth c.edges s C c.prec (t:=t.val) hu hUM hM
  change childPrecision c.prec a c.edges (stepU lam c.depth) t.val ≤ inputPrecisionCap s C (c.depth+1)
  apply hm.trans
  change c.prec+b*2^a ≤ (C*s+b*(c.depth+1))*2^priorBits lam (c.depth+1)
  rw [priorBits_next]
  change c.prec+b*2^a ≤ (C*s+b*(c.depth+1))*2^a
  have hprev : priorBits lam c.depth ≤ a := by
    rw [show a=stepA lam c.depth from rfl,bits_split]
    omega
  have h1 : c.prec ≤ (C*s+b*c.depth)*2^a :=
    hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hprev))
  calc
    _ ≤ (C*s+b*c.depth)*2^a+b*2^a := Nat.add_le_add_right h1 _
    _=_ := by ring

/-- An active source call installs its next depth even if the new
extent is a leaf, and even when its evaluation word was prescribed. -/
theorem genuine_next_depth_fits (hs : Stable s C c) (active : (SP).cutoff<c.edges) :
    c.depth+1 ≤ pathLimit s C := by
  let lam := Nat.clog 2 s
  have hLam : 0<lam := (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg)
  have cap := active_depth_power s lam C c.edges c.depth hLam active hs.sizeByDepth
  exact Nat.succ_le_succ (Nat.le_log_of_pow_le (by decide : 1<(8:ℕ)) cap)

theorem absolute_rail_reaches_suffix (seed : AbsoluteSeed s C r)
    (path : NativeReach (Plan sel) r c) : AbsoluteSeed s C c := by
  refine nativeReach_run_invariant (Plan sel)
    (fun x : Call (PhysicalHost f ell)=>AbsoluteSeed s C x) ?_ path seed
  intro p current w
  refine ⟨stable_step cfg sel current.stable w,?_ ,?_⟩
  · change p.depth+1 ≤ pathLimit s C
    exact genuine_next_depth_fits cfg current.stable w.property
  · change registerPrecision SP p w.val.1 ≤ inputPrecisionCap s C (p.depth+1)
    exact absolute_register_fits_next cfg current.stable current.prec w.property w.val.1

theorem nonprefix_zero_step_preserves_absolute_rail (seed : AbsoluteSeed s C c)
    (d : Ready SP (sourceDelta s) c) (t : Center SP c)
    (z : Box f ell (registerPrecision SP c t)) (g : Fin 64) :
    AbsoluteSeed s C (zeroChild sel d t z g) :=
  ⟨zeroChild_stable sel d t seed.stable z g,
    genuine_next_depth_fits cfg seed.stable d.active,
    absolute_register_fits_next cfg seed.stable seed.prec d.active t⟩

theorem absolute_seed_input_precision_poly (seed : AbsoluteSeed s C c) :
    c.prec ≤ 41*C*s*(Nat.clog 2 s+1)^2*2^priorBits (Nat.clog 2 s) c.depth := by
  let lam := Nat.clog 2 s
  have hLam : 0<lam := (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg)
  have hd : c.depth ≤ lam+1 := seed.depth.trans (path_limit_le s C cfg.constPos hLam cfg.size)
  apply seed.prec.trans
  unfold inputPrecisionCap
  apply Nat.mul_le_mul_right
  have hz : C*s ≤ C*s*(lam+1)^2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hp := Nat.mul_le_mul_left (40*C*s*(lam+1)) hd
  calc
    _ ≤ C*s*(lam+1)^2+(40*C*s*(lam+1))*(lam+1) := Nat.add_le_add hz hp
    _=_ := by ring
end Schedule

section Actual
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m))
local notation "R" ell => (physicalRootCall f ell base m (printedHalf m) n T
  (J6R28GeneratedRootFrame.constantRootWord m))

/-- All prescribed samples, including the non-native last positive
ordinal. The original source shape fixes the schedule at physicalSize
and uses the actual constant C=2. -/
theorem original_prescribed_exterior_seed (ell : ℕ) (i : J6Recovery.Addr m)
    (j : Fin (externalProbeDegree (physicalSize m native) (R ell)+1)) (g : Fin 64)
    (baseFit : base ≤ 2*physicalSize m native) :
    AbsoluteSeed (physicalSize m native) 2 (exteriorChild G ell i j g) := by
  let p := R ell
  have seed : AbsoluteSeed (physicalSize m native) 2 p :=
    true_depth_zero_seed (G.stable ell) rfl baseFit
  exact nonprefix_zero_step_preserves_absolute_rail (G.bounds) (G.selector ell) seed
    (G.ready ell) (G.centre ell i) _ g
end Actual

#print axioms AbsoluteSeed
#print axioms true_depth_zero_seed
#print axioms absolute_register_fits_next
#print axioms genuine_next_depth_fits
#print axioms absolute_rail_reaches_suffix
#print axioms nonprefix_zero_step_preserves_absolute_rail
#print axioms absolute_seed_input_precision_poly
#print axioms original_prescribed_exterior_seed
end J6R68AbsolutePrescribed
