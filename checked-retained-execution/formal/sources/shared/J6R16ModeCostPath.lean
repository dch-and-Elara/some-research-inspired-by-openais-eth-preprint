import J6R16ModeCostScale
import J6R12BlueprintReach

/-! Inherited precision on the actual dependent J6 packet factory.
The root is at depth zero and starts with precision at most C*s.
Every induction step is a legal generated child, including a leaf. -/
namespace J6R16ModeCost
open scoped Polynomial
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J1PPrinted

def pathLimit (s C : ℕ) : ℕ :=
  Nat.log 8 (C*(Nat.clog 2 s).sqrt)+1

def inputPrecisionCap (s C d : ℕ) : ℕ :=
  (C*s+(40*C*s*(Nat.clog 2 s+1))*d)*2^priorBits (Nat.clog 2 s) d

theorem nativeReach_run_invariant {X : Type*} (P : FinitePlan X) (F : X→Prop)
    (hs : ∀ c, F c → ∀ w : P.Slot c,F (P.child c w))
    {r c : X} (h : NativeReach P r c) (hr : F r) : F c := by
  induction h with
  | reflexive => exact hr
  | step w h ih => exact ih (hs _ hr w)

theorem active_depth_power (s lam C M d : ℕ) (hLam : 0<lam)
    (ha : J9PrintedSchedule.leafThreshold s lam<M) (h : 8^d*M≤C*s) :
    8^d≤C*lam.sqrt := by
  have hs := (J9PrintedSchedule.le_roundup_mul s lam.sqrt (Nat.sqrt_pos.mpr hLam)).trans
    (Nat.mul_le_mul_right lam.sqrt ha.le)
  have H : 8^d*M≤(C*lam.sqrt)*M := by
    calc
      _≤C*s := h
      _≤C*(M*lam.sqrt) := Nat.mul_le_mul_left C hs
      _=_ := by ring
  exact Nat.le_of_mul_le_mul_right H (Nat.zero_lt_of_lt ha)

theorem source_const_bound (lam C : ℕ) (hC : 0<C)
    (hsize : (2*epsDen)^30*C^10≤lam) : C≤lam := by
  have h := Nat.pow_le_pow_right hC (show (1:ℕ)≤10 by decide)
  rw [pow_one] at h
  exact h.trans ((Nat.le_mul_of_pos_left _ (by unfold epsDen; positivity)).trans hsize)

theorem path_limit_le (s C : ℕ) (hC : 0<C)
    (hLam : 0<Nat.clog 2 s) (hsize : (2*epsDen)^30*C^10≤Nat.clog 2 s) :
    pathLimit s C≤Nat.clog 2 s+1 := by
  let lam := Nat.clog 2 s
  have hC' := source_const_bound lam C hC hsize
  have he : C*lam.sqrt<(8:ℕ)^(lam+1) := by
    calc
      _≤lam*lam := Nat.mul_le_mul hC' (Nat.sqrt_le_self _)
      _≤(2^lam)*(2^lam) := Nat.mul_le_mul
        ((Nat.le_succ _).trans (J9PrintedSchedule.next_le_two_power _))
        ((Nat.le_succ _).trans (J9PrintedSchedule.next_le_two_power _))
      _=2^(2*lam) := by rw [← pow_add]; congr 1; omega
      _≤2^(3*lam) := Nat.pow_le_pow_right (by decide) (by omega)
      _=8^lam := by rw [pow_mul]; rfl
      _<_ := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  have ht : C*lam.sqrt≠0 := (mul_pos hC (Nat.sqrt_pos.mpr hLam)).ne'
  exact Nat.succ_le_succ (Nat.le_of_lt_succ ((Nat.log_lt_iff_lt_pow (by decide) ht).mpr he))

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))

include cfg

theorem root_lambda_large : 1024≤Nat.clog 2 s := by
  have H := (J9PrintedSchedule.rootU_range (Nat.clog 2 s)).1
  have hu := cfg.widthPos
  omega

theorem path_depth_bound {r c : Call (PhysicalHost f ell)} (h : NativeReach (Plan sel) r c)
    (hr : Stable s C r) (hzero : r.depth=0) :
    c.depth≤pathLimit s C := by
  let F (x : Call (PhysicalHost f ell)) := Stable s C x ∧ x.depth≤pathLimit s C
  have hStep (x : Call (PhysicalHost f ell)) (hx : F x) (w : (Plan sel).Slot x) :
      F ((Plan sel).child x w) := by
    have ha : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)<x.edges := w.property
    have hLam : 0<Nat.clog 2 s := (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg)
    have H := active_depth_power s (Nat.clog 2 s) C x.edges x.depth hLam ha hx.1.sizeByDepth
    have hD := Nat.le_log_of_pow_le (by decide : 1<(8:ℕ)) H
    exact ⟨stable_step cfg sel hx.1 w,Nat.succ_le_succ hD⟩
  have hroot : F r := ⟨hr,by rw [hzero]; exact Nat.zero_le _⟩
  exact (nativeReach_run_invariant (Plan sel) F hStep h hroot).2

theorem depth_le_lambda_succ {r c : Call (PhysicalHost f ell)} (h : NativeReach (Plan sel) r c)
    (hr : Stable s C r) (hzero : r.depth=0) :
    c.depth≤Nat.clog 2 s+1 :=
  (path_depth_bound cfg sel h hr hzero).trans
    (path_limit_le s C cfg.constPos ((by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg)) cfg.size)

theorem input_precision_reachable {r c : Call (PhysicalHost f ell)}
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) (hzero : r.depth=0)
    (hroot : r.prec≤C*s) :
    c.prec≤ inputPrecisionCap s C c.depth := by
  let lam := Nat.clog 2 s
  let F (x : Call (PhysicalHost f ell)) := Stable s C x ∧ x.prec≤ inputPrecisionCap s C x.depth
  have hStep (x : Call (PhysicalHost f ell)) (hx : F x) (w : (Plan sel).Slot x) :
      F ((Plan sel).child x w) := by
    refine ⟨stable_step cfg sel hx.1 w,?_⟩
    have ha : J9PrintedSchedule.leafThreshold s lam<x.edges := w.property
    obtain ⟨hu,_,huM⟩ :=
      printed_taper_legal s x.edges C x.depth cfg.widthPos cfg.constPos cfg.size ha hx.1.sizeByDepth
    have hM : x.edges≤C*s := (Nat.le_mul_of_pos_left _ (by positivity : 0<(8:ℕ)^x.depth)).trans
      hx.1.sizeByDepth
    have hm := precision_increment_bound lam x.depth x.edges s C x.prec
      (t:=w.val.1.val) hu huM hM
    let a := stepA lam x.depth
    let P := 40*C*s*(lam+1)
    change childPrecision x.prec a x.edges (stepU lam x.depth) w.val.1.val≤
      inputPrecisionCap s C (x.depth+1)
    apply hm.trans
    change x.prec+P*2^a≤(C*s+P*(x.depth+1))*2^priorBits lam (x.depth+1)
    rw [priorBits_next]
    change x.prec+P*2^a≤(C*s+P*(x.depth+1))*2^a
    have hprev : priorBits lam x.depth≤a := by
      rw [show a=stepA lam x.depth from rfl,bits_split]
      omega
    have h1 : x.prec≤(C*s+P*x.depth)*2^a :=
      hx.2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hprev))
    calc
      _≤(C*s+P*x.depth)*2^a+P*2^a := Nat.add_le_add_right h1 _
      _=_ := by ring
  have hR : F r := by
    refine ⟨hr,?_⟩
    simpa [inputPrecisionCap,hzero] using hroot
  exact (nativeReach_run_invariant (Plan sel) F hStep h hR).2

theorem input_precision_polynomial_factor {r c : Call (PhysicalHost f ell)}
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) (hzero : r.depth=0)
    (hroot : r.prec≤C*s) :
    c.prec≤41*C*s*(Nat.clog 2 s+1)^2*2^priorBits (Nat.clog 2 s) c.depth := by
  let lam := Nat.clog 2 s
  have hd : c.depth≤lam+1 := depth_le_lambda_succ cfg sel h hr hzero
  apply (input_precision_reachable cfg sel h hr hzero hroot).trans
  unfold inputPrecisionCap
  apply Nat.mul_le_mul_right
  have hz : C*s≤C*s*(lam+1)^2 :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hp := Nat.mul_le_mul_left (40*C*s*(lam+1)) hd
  calc
    _≤C*s*(lam+1)^2+(40*C*s*(lam+1))*(lam+1) := Nat.add_le_add hz hp
    _=_ := by ring

#print axioms active_depth_power
#print axioms path_limit_le
#print axioms path_depth_bound
#print axioms input_precision_reachable
#print axioms input_precision_polynomial_factor
end J6R16ModeCost



