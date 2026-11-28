import J6R57ActiveFeeSplit
import J6R57ActiveFeeMasks
import J6R57ActiveFeeWeights

/-! The source's fixed centre tariff, after the actual native mode
loop has been factored out, is polynomial in named physical fields.
Only the metered mask and weighted-tape suppliers are held opaque. -/
namespace J6R57ActiveFee
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R23ScheduleWeight J6R19Retained HermiteLoss J6R48BitCost J6R49DFS
open P1DyadicGrid

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 3450
set_option linter.unusedSectionVars false
set_option Elab.async false
attribute [local irreducible] J6R12Blueprint.printedParams

def fixedProbePx (K : ℕ) :=
  J6R16ModeCost.setupCap K K+uvPx K+128*(K+1)^4

def fixedCentrePx (K tape mask : ℕ) :=
  tape+
    (K*fixedProbePx K+normalizerPx K+K*K*(mask+K*(K+6)+uvPx K+2)+
      interpolationPx K+quotientPx K+4)+
    K*termPx K+uvPx K+K*(addPx K+2)+tapePx K+4

theorem actual_fixed_probe_widths
    {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q K : ℕ}
    {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
    {d : Ready S Δ c} {t : Center S c}
    (F : Frame f (registerPrecision S c t)) (I : J6R16ModeCost.SiteTape sel d t q)
    (cap : BitCaps F.words.length ell (registerPrecision S c t) K)
    (hq : q ≤ K) (hn : I.words.length ≤ K) :
    fixedProbe F I ≤ fixedProbePx K := by
  have u := uv_word_cap cap
  have m := delayCap_physical_poly hq hn
  have s : J6R16ModeCost.setupCap q I.words.length ≤ J6R16ModeCost.setupCap K K := by
    unfold J6R16ModeCost.setupCap
    gcongr
  exact Nat.add_le_add (Nat.add_le_add s u) m

variable {f : ℤ[X]} {ell s : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f}

theorem actual_fixed_centre_physical_envelope
    {t : Center S c} {q highPrec K tape mask : ℕ}
    (J : @CentreMachine f ell s sel c d t bank q)
    (hv : 0<ell) (hf : f.Monic) (high : Frame f highPrec) (B : ℕ)
    (field : f.natDegree ≤ K) (hℓ : ell ≤ K)
    (pLow : registerPrecision S c t ≤ K) (pHigh : highPrec ≤ K)
    (bits : @centreA f ell s c ≤ K) (ex : B ≤ K)
    (probes : @probeCount f ell s c ≤ K)
    (win : J.window ≤ K) (rows : J.roster.rows.length+1 ≤ K)
    (uPos : 0<(@centreU f ell s c)) (uFit : (@centreU f ell s c) ≤ c.edges) (orderFit : 4*c.edges ≤ K)
    (width : q ≤ K) (tapeLen : J.tape.result.words.length ≤ K)
    (readsTape : J.tape.steps ≤ tape) (readsMask : ∀ z,(J.masks z).steps ≤ mask) :
    fixedCentre J hv high B ≤ fixedCentrePx K tape mask := by
  let F := J.low
  let rs := J.roster.rows
  let a := @centreA f ell s c
  let p := @centreP f ell s c t
  let k := J.window
  let n := @probeCount f ell s c
  have lo : BitCaps f.natDegree ell p K := ⟨field,hℓ,pLow⟩
  have hi : BitCaps f.natDegree ell highPrec K := ⟨field,hℓ,pHigh⟩
  have loF : BitCaps F.words.length ell p K := ⟨(F.natDegree hf).le.trans field,hℓ,pLow⟩
  have hiF : BitCaps high.words.length ell highPrec K :=
    ⟨(high.natDegree hf).le.trans field,hℓ,pHigh⟩
  have power (x : ℤ×ℕ) (hx : x∈rs) : x.2 ≤ K :=
    (J.roster.exponents x hx).le.trans
      ((order_bound c.edges (@centreU f ell s c) x.1 uPos uFit).trans orderFit)
  have tGrid := (active_grid a c.edges (@centreU f ell s c) t.property).1
  have tNonzero := (active_grid a c.edges (@centreU f ell s c) t.property).2
  have actualCount (mode : Side) (x : ℤ×ℕ) (hx : x∈rs) : factorCount t.val mode x ≤ K*K := by
    rcases x with ⟨x,j⟩
    have count := factor_count_cap (k:=j) mode tGrid (J.roster.is_grid (x,j) hx)
      (J.roster.in_active (x,j) hx).2
      (active_grid a c.edges (@centreU f ell s c) (J.roster.in_active (x,j) hx).1).2
    exact count.trans (Nat.mul_le_mul (power (x,j) hx) bits)
  have term (j : ℕ) (hj : j∈List.range k) :
      termFee f.natDegree ell p highPrec a B k j high.hp t.val rs ≤ termPx K := by
    have jFit : j ≤ K := (List.mem_range.mp hj).le.trans win
    refine actual_term_arithmetic_cap lo hi high.hp bits ex win jFit t.val rs rows power ?_ (actualCount .den)
    intro q hq
    rcases List.mem_append.mp hq with yes | tail
    · exact actualCount .num q yes
    · rw [List.mem_singleton] at tail
      subst q
      have lv : level (-t.val) ≤ a := by rw [level_neg]; exact level_grid_le tGrid tNonzero
      exact Nat.mul_le_mul jFit (lv.trans bits)
  have aN := normalizer_arithmetic_cap loF F.hp bits win rs ((Nat.le_succ _).trans rows) power
  have aI := interpolation_arithmetic_cap loF F.hp win probes
  have aQ := quotient_arithmetic_cap loF F.hp win
  have aT := jet_tape_cap loF win
  have aP := actual_fixed_probe_widths F J.tape.result loF width tapeLen
  have aM := exact_probe_mask_read_envelope F.hp hv J.masks loF.degree hℓ pLow probes readsMask
  have aUb := uv_word_cap hiF
  have aAdd := addition_cap hiF high.hp
  change ((probeOrder n).map (needsAt (fun i=>padCost (encodeProbe F.hp hv (J.masks i).result)
    (J.masks i).steps))).sum ≤ K*K*(mask+K*(K+6)+uvPx K+2) at aM
  have aW₀ := actual_list_charges (List.range k) (fun j=>termFee f.natDegree ell p
    highPrec a B k j high.hp t.val rs) (termPx K) term
  rw [List.length_range] at aW₀
  have aW : ((List.range k).map (fun j=>termFee f.natDegree ell p highPrec a B k j
    high.hp t.val rs)).sum ≤ K*termPx K := aW₀.trans (Nat.mul_le_mul_right _ win)
  unfold fixedCentre fixedCentrePx
  dsimp only
  gcongr

#print axioms actual_fixed_probe_widths
#print axioms actual_fixed_centre_physical_envelope
end J6R57ActiveFee
