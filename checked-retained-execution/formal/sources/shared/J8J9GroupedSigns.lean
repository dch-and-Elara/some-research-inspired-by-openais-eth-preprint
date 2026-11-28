import J8J9GroupedReadout

/- Changes in elaborating imported chart enumerations can flag theorem-scope instances. This affects only the unused-section-variable style linter. -/
set_option linter.unusedSectionVars false

/-! One complete physical tile: bits from exactly the selected high finite
probes at the printed root precision. This is readout correctness, not a
claim that the probes must be computed by a particular execution method. -/

namespace J8J9Grouped
open scoped BigOperators Polynomial Classical
open Polynomial NativeProbeRing DyadicProbeCompiler J8Physical J8EndToEnd

noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def tileReadout (e : EndpointSeating d) (even : Even L) (hL : 2 < L) (hm : 0 < M)
    (k : ℕ) (a : S) (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (q : ℕ) (hpq : 10*M ≤ q) (f : ℤ[X]) (hf : f.Monic)
    (addr : Fin (10*M+1) → Fin f.natDegree → Bool) : ℚ :=
  let x := fun j => probe (10*M) f (addr j)
  let obs := fun j => reduceScalar (10*M) q hpq f
    (highObservation d e even hL a F sign tail b kt k q f (addr j))
  readRational (10*M) f hf (clear d a b) (NativeInterpolation.decode x obs ⟨1,by omega⟩)

def tileSignReadout (e : EndpointSeating d) (even : Even L) (a : S) (F : OldTables d)
    (sign : S → Bool) (higher : RestArguments d)
    (obs : Fin (Fintype.card (PinTile d a)) → ℚ) : Fin (Fintype.card (PinTile d a)) → Bool :=
  let gs := d.pinLabel a
  let gt := d.rowLabel (pinWire d a).1
  let src := localChild d e even gs (outerAmplitude L) (F gs)
  let tgt := localChild d e even gt (outerAmplitude L) (F gt)
  let scale := fun b : Fin (Fintype.card (PinTile d a)) =>
    J8SourceMoment.completedScale (publicSiblings d e even a F higher sign) src tgt
      (groupedTargets d a) (2*(L:ℚ)) (physicalDenominator d a) b
  NativeMomentReconstruction.decodeBits (coordinates d a) scale
    (J8SourceMoment.nonpinBackground src (fun b => tileBackground d a b)) obs

theorem recover_tile_signs_from_high (e : EndpointSeating d) (even : Even L) (hL : 3 ≤ L)
    (k : ℕ) (length : L = 2^k) (a : S)
    (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a) (idx : Wire R ≃ Fin M)
    (hM : L^3 ≤ M) (capacity : L * Fintype.card Packet ≤ 3*M)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d) (higher : RestArguments d)
    (sat : ∀ g v, ∃ x, LiteralPortCompiler.satisfied (F g v) x = true)
    (kt : Fin (Fintype.card (PinTile d a)) → TargetPorts d a → Source[X])
    (q : ℕ) (hpq : 10*M ≤ q)
    (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree) [Fact (Irreducible (residuePoly f))]
    (addr : Fin (10*M+1) → Fin f.natDegree → Bool) (distinct : Function.Injective addr) :
    have hm : 0 < M := (show 0 < L^3 by positivity).trans_le hM
    tileSignReadout d e even a F sign higher
      (fun b => tileReadout d e even (by omega) hm k a F sign tail b (kt b) q hpq f hf addr) =
      fun i => sign (pinEnumeration d a i).1 := by
  have raw := recover_physical_tile_exact d e even a (by omega) off F higher sign sat (fun _ _ => 0)
  dsimp only at raw
  unfold tileSignReadout
  dsimp only
  convert raw using 2
  funext b
  exact highObservation_readout d e even hL k length a off idx hM capacity F sign tail higher b
    (kt b) (fun _ => 0) q hpq f hf hd addr distinct

section Schedule

variable (s M : ℕ)
local notation "lambda" => Nat.clog 2 s
local notation "len" => J9PrintedSchedule.rootL lambda
local notation "u" => J9PrintedSchedule.rootU lambda
local notation "k" => J9PrintedSchedule.rootA lambda

theorem recover_printed_tile_signs
    (d : Layout Packet R S V G P len) (e : EndpointSeating d)
    (a : S) (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (idx : Wire R ≃ Fin M) (capacity : len * Fintype.card Packet ≤ 3*M)
    (hLambda : 262144 ≤ lambda) (hActive : J9PrintedSchedule.leafThreshold s lambda < M)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d) (higher : RestArguments d)
    (sat : ∀ g v, ∃ x, LiteralPortCompiler.satisfied (F g v) x = true)
    (kt : Fin (Fintype.card (PinTile d a)) → TargetPorts d a → Source[X])
    (baseP : ℕ) (hP : 0 < baseP) (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))] (fit : J9PrintedSchedule.probeCount M len ≤ 2^f.natDegree) :
    let numProbes := J9PrintedSchedule.probeCount M len
    let q := J9PrintedSchedule.precision baseP ((3*M+u-1)/u) len M k
    have hlen : 6 ≤ len := (J9PrintedSchedule.rootL_ge_six_iff_lambda lambda).2 hLambda
    have heven : Even len := by
      have hu : 1 ≤ u := le_trans (by decide) ((J9PrintedSchedule.rootL_ge_six_iff_u lambda).1 hlen)
      have ho := J9PrintedSchedule.root_outer_odd lambda hu
      exact ⟨len/2, by omega⟩
    have hk : 1 ≤ k := by
      have hu := (J9PrintedSchedule.rootL_ge_six_iff_u lambda).1 hlen
      unfold J9PrintedSchedule.rootA
      omega
    have hpq : 10*M ≤ q := (J9PrintedSchedule.precision_gt_ten _ _ _ _ _ hP hk).le
    have hfewer : 10*M+1 ≤ numProbes := J9PrintedSchedule.probes_ge_ten_add_one M len hlen
    have hm : 0 < M := by omega
    let addr := fun i => chosenRep f.natDegree numProbes fit (Fin.castLE hfewer i)
    tileSignReadout d e heven a F sign higher
      (fun b => tileReadout d e heven (by omega) hm k a F sign tail b (kt b) q hpq f hf addr) =
      fun i => sign (pinEnumeration d a i).1 := by
  dsimp only
  apply recover_tile_signs_from_high
  · exact le_trans (by decide) ((J9PrintedSchedule.rootL_ge_six_iff_lambda lambda).2 hLambda)
  · rfl
  · exact off
  · exact idx
  · exact J9PrintedSchedule.root_cube_le_active_M s M hActive
  · exact capacity
  · exact sat
  · exact hd
  · intro i j hij
    have e := chosenRep_injective _ _ fit hij
    exact Fin.ext (congrArg (fun z : Fin (J9PrintedSchedule.probeCount M len) => z.val) e)

end Schedule

#print axioms recover_tile_signs_from_high
#print axioms recover_printed_tile_signs
end
end J8J9Grouped
