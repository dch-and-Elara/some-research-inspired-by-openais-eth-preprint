import J6R85ScopeProducerAtlas
import J6R66LeafTariffNumbers
import J6R79NumericPrinted

/-! The mode code is the width of the one-based physical variable
rank, not the rank of an exponent tuple or an encoded ancestry path.
This section proves feasibility of a small choice. It does not assert
that a general online supplier actually makes that choice. -/
namespace J6R88ScopeCode
open scoped Polynomial Classical
open Polynomial J6R26DescriptorTree J6R34RootAtlas J6R33GeneratedChildSite
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R51Online J6R50SourceProducer
open J6R16ModeCost J6R58LeafScale J6R66LeafTariff J6R85ScopeProducer J6R57ScopeFee

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4200
set_option maxHeartbeats 16000000

def leastRosterCode (n : ℕ) : ℕ := Nat.clog 2 (n+2)

theorem exact_roster_code_fit (n k : ℕ) :
    1+n<2^k ↔ leastRosterCode n≤k := by
  unfold leastRosterCode
  rw [Nat.clog_le_iff_le_pow (by decide : 1<(2:ℕ))]
  omega

theorem least_roster_code_positive (n : ℕ) : 0<leastRosterCode n := by
  unfold leastRosterCode
  exact Nat.clog_pos (by decide) (by omega)

def printedRosterCap (s C p0 : ℕ) : ℕ := 3*(C*s)*(p0+160*C*s^2)

def canonicalSourceCode (s C p0 : ℕ) : ℕ := leastRosterCode (printedRosterCap s C p0)

theorem canonical_code_polynomial_from_source (s C p0 : ℕ) :
    canonicalSourceCode s C p0≤printedRosterCap s C p0+2 :=
  J6R79Numeric.printed_clog_le_size _

theorem canonical_code_logarithmic_at_real_printed_receiver
    (s C p0 : ℕ) (large : 1024≤Nat.clog 2 s)
    (constant : C≤s) (receiver : p0≤161*C*s^2) :
    canonicalSourceCode s C p0≤6*Nat.clog 2 s := by
  have prec : p0+160*C*s^2≤321*C*s^2 := by
    calc
      _≤161*C*s^2+160*C*s^2 := Nat.add_le_add_right receiver _
      _=_ := by ring
  have hr := native_mode_count_at_absolute_receiver
    (modes:=printedRosterCap s C p0) (p:=p0+160*C*s^2) large constant prec
      (Nat.le_refl (printedRosterCap s C p0))
  exact (Nat.clog_le_iff_le_pow (by decide : 1<(2:ℕ))).2 hr

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "Plan₀" => (@Plan f ell s sel)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)

theorem exact_native_roster_code_lower_and_choice
    (p : Path sel r c) (w : (Plan₀).Slot c)
    (I : OccurrenceInput T (p.ticket w) key prec tw bw page) :
    leastRosterCode I.geometry.modes.length≤I.code ∧
    leastRosterCode I.geometry.modes.length≤canonicalSourceCode s C r.prec ∧
    1+I.geometry.modes.length<2^(canonicalSourceCode s C r.prec) := by
  let v := p.ticket w
  let d := ticketReady T v
  let low := registerPrecision SP c v.centerAt
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have card : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact d.edgeCount
  have e := actual_source_path_edges_le (cfg:=cfg) sel T.rootStable p
  have hp := actual_native_register_quadratic (cfg:=cfg) sel T.rootStable p w.property v.centerAt
  have m := actual_mode_roster_fits_padded_area I.geometry
  change I.geometry.modes.length≤3*Nat.card c.host.Edge*low at m
  rw [card] at m
  have hRoster : I.geometry.modes.length≤printedRosterCap s C r.prec :=
    m.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ e) hp)
  have fit : printedRosterCap s C r.prec+2≤2^(canonicalSourceCode s C r.prec) :=
    Nat.le_pow_clog (by decide) _
  have legal : 1+I.geometry.modes.length<2^(canonicalSourceCode s C r.prec) := by omega
  exact ⟨(exact_roster_code_fit _ _).1 I.codeFit,(exact_roster_code_fit _ _).1 legal,legal⟩

theorem true_atlas_from_bounded_native_code_choice
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) (w : (Plan₀).Slot c)
    (receiver : r.prec≤161*C*s^2)
    (selection : (sourceState M p w).input.code≤canonicalSourceCode s C r.prec) :
    AtlasFootprint (sourceState M p w).input
      (atlasSourceRoof s C r.prec ell page tw bw (6*Nat.clog 2 s)) :=
  actual_atlas_footprint_from_printed_source p w (sourceState M p w).input _ (selection.trans
    (canonical_code_logarithmic_at_real_printed_receiver s C r.prec
      (root_lambda_large cfg) cfg.constSmall receiver))

#print axioms exact_roster_code_fit
#print axioms least_roster_code_positive
#print axioms canonical_code_polynomial_from_source
#print axioms canonical_code_logarithmic_at_real_printed_receiver
#print axioms exact_native_roster_code_lower_and_choice
#print axioms true_atlas_from_bounded_native_code_choice
end
end J6R88ScopeCode
