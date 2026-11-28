import J8RelaxedChart
import J6R16SpecializedBoxReadReceipt
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace J8Physical.Relaxed
open scoped Classical BigOperators Polynomial
open Polynomial NativeProbeRing DyadicProbeCompiler J8EndToEnd J8J9Grouped
open J9R13PhysicalFusion J9R13PhysicalTables J9R13ChartFirst
open LiteralPortCompiler J9LayoutTransfer J6R14SpecializedBox J6R9Recursive
noncomputable section
local instance (priority := 10000) relaxedReceiptsFinDecEq (n : ℕ) : DecidableEq (Fin n) :=
  fun i j => Classical.propDecidable (i=j)
variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
theorem chart_one_hit (a : S) (idx : J8Physical.Wire R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) (e : RowEndpointSeating d) :
    ∀ r, ¬ ((J9End.chart d a idx truth).hit r false = true ∧
      (J9End.chart d a idx truth).hit r true = true) := by
  intro r h
  obtain ⟨y,hy⟩ := (J9End.hit_true_iff d (r,false)).mp h.1
  obtain ⟨z,hz⟩ := (J9End.hit_true_iff d (r,true)).mp h.2
  have bad := row_hit_unique d e hy hz rfl
  exact Bool.false_ne_true (congrArg Prod.snd bad)

set_option maxHeartbeats 4000000 in
theorem read_chart_from_same_children
    (e : RowEndpointSeating d) (even : Even L) (hL : 3 ≤ L) (k : ℕ) (hpow : L=2^k)
    (a : S) (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (idx : Wire R ≃ Fin M) (hCube : L^3≤M) (capacity : L * Fintype.card Packet≤3*M)
    (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a→Source[X])
    (rows : (Fin M→Bool)→R→Bool→ℚ[X]) (cross : Fin L→ℚ[X]) (source : (Fin M→Bool)→ℚ[X])
    (q : ℕ) (hpq : 10*M≤q) (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))] (fit : 10*M+1≤2^f.natDegree) :
    let g := J9End.chart d a idx (satisfied (globalCNF d idx F sign))
    let x := fun i => probe (10*M) f (chosenRep f.natDegree (10*M+1) fit i)
    let y := fun i => reduceScalar (10*M) q hpq f
      (highObservation d e even (by omega) a F sign tail b kt k q f
        (chosenRep f.natDegree (10*M+1) fit i))
    ((projectBase (10*M) f hf ((J9FactorBounds.publicDenominator g b : Scalar (10*M) f) *
      NativeInterpolation.decode x y ⟨1, by
        have hM : 0<M := (show 0<L^3 by positivity).trans_le hCube
        omega⟩)).valMinAbs : ℚ) / J9FactorBounds.publicDenominator g b =
      (J9End.literalCompleted g b rows cross source).coeff 1 := by
  dsimp only
  let truth := satisfied (globalCNF d idx F sign)
  let g := J9End.chart d a idx truth
  have hhL : 2<L := by omega
  have he : L%2=0 := by obtain ⟨u,hu⟩ := even; omega
  have hB : b.val<L := (b.isLt.trans_le (pins_per_tile d a even)).trans_le (Nat.div_le_self _ _)
  have hPar : ∀ i∈g.targets, i.val%2=g.tau.val%2 := by
    intro i hi
    rw [Nat.mod_eq_of_lt g.tau.isLt]
    exact J9End.chart_parity d a idx truth i hi
  let U := literalSystem d idx F sign
  let B := literalBase d e even a idx tail b
  let K := literalKernel d (M:=M) even hhL a b kt
  let E := k+1+b.val
  have hExact : (2:ℚ)^E * rationalMap
    ((MvPolynomial.coeff β (completed U B K)).coeff 0) =
      (J9End.literalCompleted g b rows cross source).coeff 1 :=
    exactFirst_from_seated_children d e even hhL a off idx F sign tail b kt k hpow rows cross source
  have hNum := (J9FactorBounds.cleared_exact_odd g b hL he hPar).2
  rw [← J9End.literal_first_exact g b rows cross source,← hExact] at hNum
  have hInSource : algebraMap ℤ Source (J9FactorBounds.publicDenominator g b) *
      (2:Source)^E * (MvPolynomial.coeff β (completed U B K)).coeff 0 =
      algebraMap ℤ Source (J9FactorBounds.exactCleared g b) := by
    apply rationalMap_injective
    have hint (a : ℤ) : rationalMap (algebraMap ℤ Source a) = (a : ℚ) :=
      IsLocalization.lift_eq oddRatUnit a
    simpa only [hint,map_mul,map_pow,map_ofNat,mul_assoc] using hNum.symm
  have hV : 1≤E := by unfold E; omega
  have read := J9End.recover_literal_first_from_high_samples g b hL he hB hCube hPar
    (J9End.chart_tile_injective d a idx truth) (chart_one_hit d a idx truth e)
    (J9End.chart_active_rows_budget d a idx truth capacity)
    rows cross source q hpq f hf hd fit U B K (fun _ : Unit => E) () hV hInSource
  dsimp only at read
  have hBridge (addr : Fin f.natDegree→Bool) :
      J9End.observation q f addr U B K (fun _ : Unit => E) () =
        highObservation d e even hhL a F sign tail b kt k q f addr :=
    observation_is_physical_child_product d e even hhL a off idx F sign tail b kt k q f addr
  simp only [hBridge] at read
  exact read

set_option maxHeartbeats 2200000 in
theorem signed_first_from_verified_receipts
    (e : RowEndpointSeating d) (he : Even L) (hL : 3≤L) (a : ℕ) (hpow : L=2^a)
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (idx : Wire R≃Fin M) (hCube : L^3≤M) (capacity : L*Fintype.card Packet≤3*M)
    (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (n : Fin (Fintype.card (PinTile d s))) (kt : TargetPorts d s→Source[X])
    (rows : (Fin M→Bool)→R→Bool→ℚ[X]) (cross : Fin L→ℚ[X]) (source : (Fin M→Bool)→ℚ[X])
    (q ell : ℕ) (hpq : 10*M≤q) (hℓ : 0<ell) (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (residuePoly f))] (fit : 10*M+1≤2^f.natDegree)
    (received : Fin (10*M+1)→Box f ell q)
    (hReceived : ∀ i, received i = J6ActiveInterpolation.scalarIn q f ell
      (highObservation d e he (by omega) s F sign tail n kt a q f
        (chosenRep f.natDegree (10*M+1) fit i))) :
    let chart := J9End.chart d s idx (satisfied (globalCNF d idx F sign))
    let x := fun i => probe (10*M) f (chosenRep f.natDegree (10*M+1) fit i)
    let y := fun i => reduceScalar (10*M) q hpq f (atZero q f ell hℓ (received i))
    ((projectBase (10*M) f hf ((J9FactorBounds.publicDenominator chart n:Scalar (10*M) f) *
      NativeInterpolation.decode x y ⟨1, by
        have hM : 0<M := (show 0<L^3 by positivity).trans_le hCube
        omega⟩)).valMinAbs:ℚ) / J9FactorBounds.publicDenominator chart n =
      (J9End.literalCompleted chart n rows cross source).coeff 1 := by
  dsimp only
  simp_rw [hReceived,atZero_scalarIn]
  exact read_chart_from_same_children d e he hL a hpow s off idx hCube capacity
    F sign tail n kt rows cross source q hpq f hf hd fit

#print axioms chart_one_hit
#print axioms read_chart_from_same_children
#print axioms signed_first_from_verified_receipts
end
end J8Physical.Relaxed