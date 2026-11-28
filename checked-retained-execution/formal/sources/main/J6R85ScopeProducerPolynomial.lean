import J6R85ScopeProducerAtlas
import J6R79NumericPolynomial
import J6R79NumericPrinted

/-! The actual atlas producer steps have a fixed source polynomial.
The same StoredSite and same compilePages Meter are used throughout. -/
namespace J6R85ScopeProducer
open scoped Polynomial Classical
open Polynomial J6R32StatefulArithmetic J6R24MeteredRecursion J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R34RootAtlas
open J6R30ProducedGateRegistry J6R51Online J6R50SourceProducer J6R57ScopeFee

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4100
set_option maxHeartbeats 12500000

theorem atlasSourceRoof_fixed_degree {s C p0 ell page tw bw code K : ℕ}
    (hs : s≤K) (hC : C≤K) (hp : p0≤K) (hl : ell≤K)
    (hpg : page≤K) (ht : tw≤K) (hb : bw≤K) (hc : code≤K) :
    atlasSourceRoof s C p0 ell page tw bw code ≤ 2^12*(K+1)^6 := by
  have hLog : Nat.clog 2 s≤K := (J6R79Numeric.printed_clog_le_size s).trans hs
  unfold atlasSourceRoof
  calc
    _ ≤ (2*K)^6+(K+1)+3*(K*K)+(K+160*K*K^2)+
      (K+4*K+K)+3*(K*K)*(K+160*K*K^2)+K+K := by gcongr
    _ ≤ _ := by ring_nf; omega

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (@Plan f ell s sel)

theorem actual_native_atlas_bill_from_geometry
    (p : Path sel r c) (w : (P).Slot c)
    (I : OccurrenceInput T (p.ticket w) key prec tw bw page)
    (code : ℕ) (codeWidth : I.code≤code) :
    (compileOccurrence I).compilePages.steps≤
      2^26*(atlasSourceRoof s C r.prec ell page tw bw code+1)^8 := by
  let U := atlasSourceRoof s C r.prec ell page tw bw code
  have foot := actual_atlas_footprint_from_printed_source p w I code codeWidth
  have decompose := (compiled_occurrence_priced_by_actual_producers_and_chart I).2
  have nonnegative : atlasWordGeometryCeiling U≤J6R79Numeric.structuralScope U := by
    unfold J6R79Numeric.structuralScope
    omega
  exact decompose.trans ((literal_atlas_tariff_from_finite_footprint I U foot).trans
    (nonnegative.trans (J6R79Numeric.structural_scope_is_polynomial U)))

theorem same_online_atlas_compile_is_polynomial
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) (w : (P).Slot c)
    (code K : ℕ) (codeWidth : (sourceState M p w).input.code≤code)
    (hs : s≤K) (hC : C≤K) (hp : r.prec≤K) (hl : ell≤K)
    (hpg : page≤K) (ht : tw≤K) (hb : bw≤K) (hc : code≤K) :
    (sourceState M p w).birth.compilePages.steps≤2^130*(K+1)^48 := by
  let U := atlasSourceRoof s C r.prec ell page tw bw code
  have sized : U≤2^12*(K+1)^6 := atlasSourceRoof_fixed_degree hs hC hp hl hpg ht hb hc
  have unit : 1≤(K+1)^6 := Nat.succ_le_of_lt (by positivity)
  have sized' : U+1≤2^13*(K+1)^6 := by
    calc
      _ ≤ 2^12*(K+1)^6+(K+1)^6 := Nat.add_le_add sized unit
      _ ≤ _ := by ring_nf; omega
  change (compileOccurrence (sourceState M p w).input).compilePages.steps≤_
  exact (actual_native_atlas_bill_from_geometry p w (sourceState M p w).input code codeWidth).trans
    (calc
      2^26*(U+1)^8 ≤ 2^26*(2^13*(K+1)^6)^8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left sized' 8)
      _ ≤ _ := by ring_nf; omega)

#print axioms atlasSourceRoof_fixed_degree
#print axioms actual_native_atlas_bill_from_geometry
#print axioms same_online_atlas_compile_is_polynomial
end
end J6R85ScopeProducer
