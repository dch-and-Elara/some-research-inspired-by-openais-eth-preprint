
import A2R45LiteralRoot
import A2R45LiteralStockRead

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9500000
set_option synthInstance.maxHeartbeats 120000
set_option maxRecDepth 2150
set_option linter.unusedSectionVars false

/-! A2 on the stock source probe roster. It proves the actual one-call
case only if zero is installed, and otherwise uses the identical
active-mode slot at each actual probe index. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R12Blueprint J1PPrinted
open FixedHostAcquisition J6R11Blueprint

noncomputable section
variable {n : ℕ} (W : Plan n) (w : Input n) (f : ℤ[X])
local notation "m" => simCount n
local notation "s" => A1R43Literal.starSize m
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s
local notation "root" => rootCall W w f

theorem A2_on_stock_roster (guard : A1R43Literal.PrintedMargins m)
    (d : @J6R12Blueprint.Ready f 1 S Δ root) (cfg : RootBounds s 1 f)
    (hf : f.Monic) (hF : 0<f.natDegree) (hn : 0<n)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    let t := negativeCenter W w f guard
    let sel := fixedSelector W w f guard
    (∃ z : Probe S root, @stockWord f s root d z=(fun _=>false) ∧
      @installedRead f s sel root d t hf z=count w.enabled) ∨
    ((∀ z : Probe S root,@stockWord f s root d z≠fun _=>false) ∧
      @installedInterpolationRead f s sel root d t hf=count w.enabled) := by
  intro t sel
  by_cases h : ∃ z : Probe S root,@stockWord f s root d z=(fun _=>false)
  · obtain ⟨z,hz⟩ := h
    refine Or.inl ⟨z,hz,?_⟩
    rw [@installedRead_is_binary_read f s sel root d t hf z,hz]
    exact actual_fixed_slot_integer W w f guard d cfg hf hF hn
  · have hmiss (z : Probe S root) : @stockWord f s root d z≠fun _=>false :=
      fun hz=>h ⟨z,hz⟩
    refine Or.inr ⟨hmiss,?_⟩
    rw [@installedInterpolationRead_is_same_mode f s sel root d t hf hmiss]
    exact same_mode_when_zero_omitted W w f guard d cfg hf hF hn (@stockRosterNoZero f s root d hmiss)

omit W w in
theorem stock_probe_count_bound {c : Call (PhysicalHost f 1)}
    (d : Ready (printedParams (f:=f) (ell:=1) s) Δ c) :
    Fintype.card (Probe (printedParams (f:=f) (ell:=1) s) c) ≤2*c.edges^2+1 := by
  let a := (printedParams (f:=f) (ell:=1) s).levelBits c.depth
  let L : ℕ := 2^a
  let D := J9PrintedSchedule.arrayCard a
  have hp : 1≤D := Nat.succ_le_of_lt (by unfold D J9PrintedSchedule.arrayCard; positivity)
  have hs : L*D≤c.edges := d.paddedSlots
  have hL : L≤c.edges := by
    exact (by simpa only [mul_one] using Nat.mul_le_mul_left L hp : L≤L*D).trans hs
  rw [Fintype.card_fin]
  change c.edges*(2*L-1)+1≤2*c.edges^2+1
  have hh : c.edges*(2*L-1)≤c.edges*(2*c.edges) :=
    Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ hL))
  calc
    _ ≤ c.edges*(2*c.edges)+1 := Nat.add_le_add_right hh 1
    _ = _ := by ring

#print axioms A2_on_stock_roster
#print axioms stock_probe_count_bound
end
end A2R45Literal
