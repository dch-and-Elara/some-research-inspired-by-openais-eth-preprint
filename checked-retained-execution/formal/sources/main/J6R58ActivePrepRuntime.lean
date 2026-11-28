import J6R58ActivePrepCentre
import J6R57ActiveFeeCombine

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 18500000
set_option maxRecDepth 1700
set_option linter.unusedSectionVars false
set_option Elab.async false

/-! Bind the once-mounted physical probe table to the same online
Plan. There is no per-node or per-centre chart rebuild. The prior
non-mask preparation is still explicitly measured. -/
namespace J6R58ActivePrep
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R24MeteredRecursion J6R49DFS J6R57ActiveFee
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R51Online J6R55CachedLedger

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q n : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {fit : n≤2^f.natDegree}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

def chartMountFee : ℕ := 4

def ChartCovers (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (r : Call (PhysicalHost f ell)) (n : ℕ) : Prop :=
  ∀ (z : Sigma (Path sel r)), (S).cutoff<z.1.edges→@probeCount f ell s z.1≤n

def remaskPrepared {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
    (B : MaskTable f.natDegree n fit) (covers : @probeCount f ell s c≤n)
    (A : Meter (ActiveMachine sel d T.bank q)) : Meter (ActiveMachine sel d T.bank q) :=
  ⟨activeWithChart hf B covers A.result,A.steps+chartMountFee⟩

def withActiveChart (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) : Machine :=
  { M with
    activeRoot := fun a=>remaskPrepared (T:=T) B (covers ⟨r,.root⟩ a) (M.activeRoot a)
    activeAfter := fun p w X a=>
      remaskPrepared (T:=T) B (covers ⟨_,.step p w⟩ a) (M.activeAfter p w X a) }

/-- The only full tape copy is the separately billed installation. -/
def installActiveChart (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) : Meter Machine :=
  let R := B.install
  ⟨withActiveChart M R.result covers,R.steps+4⟩

theorem install_active_chart_exact (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) :
    installActiveChart M B covers=⟨withActiveChart M B covers,6+n*(3*f.natDegree+5)⟩ := by
  simp only [installActiveChart,B.installed_exact]
  exact congrArg (Meter.mk (withActiveChart M B covers)) (by omega)

theorem same_source_state (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) (p : Path sel r c) (w : (P).Slot c) :
    sourceState (withActiveChart M B covers) p w=sourceState M p w := by
  induction p with
  | root => rfl
  | step p prior ih =>
    change ((M.demand (sourceState (withActiveChart M B covers) p prior) w).result.advance).next=
      ((M.demand (sourceState M p prior) w).result.advance).next
    rw [ih prior]

theorem exact_prepared_active (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) (p : Path sel r c) (a : (S).cutoff<c.edges) :
    preparedActive (withActiveChart M B covers) p a =
      remaskPrepared (T:=T) B (covers ⟨c,p⟩ a) (preparedActive M p a) := by
  cases p with
  | root => rfl
  | step p w =>
    change remaskPrepared (T:=T) B _ (M.activeAfter p w
      (sourceState (withActiveChart M B covers) p w) a)=_
    rw [same_source_state]
    rfl

theorem same_cached_births (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) :
    @borns f ell s C key prec tw bw page q cfg sel r hf T (withActiveChart M B covers)=
      @borns f ell s C key prec tw bw page q cfg sel r hf T M := by
  funext x p w
  unfold borns
  rw [same_source_state]

theorem same_mounted_widths (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) {K seed : ℕ} (h : ActualMountWidths M K seed) :
    ActualMountWidths (withActiveChart M B covers) K seed := by
  refine ⟨h.edges,h.labelLanes,h.keyBits,h.precisionWord,h.pageBits,h.bodyBits,?_,?_,h.bootBodies⟩
  · intro c p w
    rw [same_source_state]
    exact h.portBits p w
  · intro c p w
    rw [same_source_state]
    exact h.ownerBits p w

include T in
theorem real_probe_count_cap (p : Path sel r c) (K : ℕ) (cs : PrintedCentreScale s C K) :
    @probeCount f ell s c≤K := by
  have E := physical_edges_at_most_root_scale (cfg:=cfg) p T.rootStable
  have b := bits_le_lam (Nat.clog 2 s) c.depth
  have t : (2:ℕ)^((S).levelBits c.depth) ≤ 2^(Nat.clog 2 s) := Nat.pow_le_pow_right (by decide) b
  apply le_trans _ cs.probes
  change c.edges*(2*2^((S).levelBits c.depth)-1)+1≤_
  exact Nat.add_le_add_right (Nat.mul_le_mul E ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left 2 t))) _

include T in
theorem live_probe_prefix (K : ℕ) (cs : PrintedCentreScale s C K) :
    ChartCovers sel r (min K (2^f.natDegree)) := by
  intro z a
  have d := ready_reachable cfg sel z.2.reached T.rootStable a
  exact Nat.le_min.mpr ⟨real_probe_count_cap (T:=T) z.2 K cs,d.fit⟩

theorem actual_installed_mask_fee (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) (p : Path sel r c) (a : (S).cutoff<c.edges)
    (K : ℕ) (cs : PrintedCentreScale s C K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (t : Center S c) (z : Probe S c) :
    ((((preparedActive (withActiveChart M B covers) p a).result).tape t).masks z).steps≤
      K*(3*K+5) := by
  rw [exact_prepared_active]
  change (((activeWithChart hf B (covers ⟨c,p⟩ a) (preparedActive M p a).result).tape t).masks z).steps≤_
  rw [active_mask_fee]
  have nz := (Nat.succ_le_of_lt z.isLt).trans (real_probe_count_cap (T:=T) p K cs)
  have ne : f.natDegree≤K := by simpa only [cfg.coefficient] using ws.field
  exact Nat.mul_le_mul nz (Nat.add_le_add_right (Nat.mul_le_mul_left 3 ne) 5)

#print axioms install_active_chart_exact
#print axioms same_source_state
#print axioms exact_prepared_active
#print axioms same_cached_births
#print axioms same_mounted_widths
#print axioms real_probe_count_cap
#print axioms live_probe_prefix
#print axioms actual_installed_mask_fee
end
end J6R58ActivePrep

