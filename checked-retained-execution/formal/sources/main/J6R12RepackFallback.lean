import J6R11IntegralFrozenRun
import J6R9RecursiveProbes

/-! The fallback reads the constant coefficient of the correctly
interpolated native local polynomial. It neither assumes that the binary
menu contains zero nor receives a free response at z=0. -/
namespace J6R12Repack
open scoped Polynomial BigOperators
open Polynomial J6ActiveRun J6R9Recursive J6ActiveSchedule J6ActiveUniqueness
open J6ActivePrintedHermite J6R11Integral

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {S : Shape Host Mode} {f : ℤ[X]} {ell : ℕ} {B : Blueprint S f ell}

/-- Actual replies of the given program, not its reference answers. -/
noncomputable def runtimeReplies (B : Blueprint S f ell) (c : Call Host) :
    Responses S f ell c :=
  fun w => B.program.run (B.program.child c w)

theorem runtime_replies_exact (D : FrozenLayout B) (grouped : D.ExactGrouped)
    (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (c : Call Host) (hc : D.Valid c) (ha : S.cutoff < c.edges) :
    runtimeReplies B c = (fun w => B.expect (B.program.child c w)) := by
  funext w
  exact D.run_exact grouped hf hd (B.program.child c w) (D.child_valid c hc ha w)

set_option maxHeartbeats 1800000 in
/-- Feed the source decoder all of the actual grouped binary probe
values computed from recursive calls. This is before Hermite
normalization, so the constant is the true Taylor value at z=0. -/
theorem runtime_local_exact (D : FrozenLayout B) (grouped : D.ExactGrouped)
    (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (c : Call Host) (hc : D.Valid c) (ha : S.cutoff < c.edges) (t : Center S c) :
    decodedAt S f ell c (D.fit c hc ha) (runtimeReplies B c) t =
      ((D.active c hc ha).jet t.val).map (reduce (registerPrecision S c t) f ell) := by
  rw [runtime_replies_exact D grouped hf hd c hc ha]
  have hp : 0 < registerPrecision S c t :=
    (Nat.zero_le c.prec).trans_lt (child_monotone _ _ _ _ _ (Nat.zero_lt_of_lt ha))
  have hD : ((D.active c hc ha).jet t.val).natDegree ≤
      J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth) := by
    rw [← natDegree_map_eq_of_injective (embed_inj f hf ell), (D.active c hc ha).integral t]
    exact (atNode_degree _ _ _).trans (D.active c hc ha).degree
  exact decodedAt_exact S f hf hd ell c (D.fit c hc ha) _ t hp _
    (natDegree_map_le.trans hD) (grouped c hc ha t)

theorem runtime_zero_exact (D : FrozenLayout B) (grouped : D.ExactGrouped)
    (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (c : Call Host) (hc : D.Valid c) (ha : S.cutoff < c.edges) (t : Center S c) :
    (decodedAt S f ell c (D.fit c hc ha) (runtimeReplies B c) t).eval 0 =
      reduce (registerPrecision S c t) f ell (((D.active c hc ha).jet t.val).coeff 0) := by
  rw [runtime_local_exact D grouped hf hd c hc ha t, ← coeff_zero_eq_eval_zero,coeff_map]

omit [Fintype Mode] [DecidableEq Mode] in
/-- Count the labelled (centre, binary-probe) acquisitions for a
prescribed all-sample fallback. This counts top-level table positions,
not individual mode children or their bit work. -/
theorem fallback_table_cells (S : Shape Host Mode) (c : Call Host) (m : ℕ) :
    Nat.card (Fin (m+1) × Probe S c) =
      (m+1)*J9PrintedSchedule.probeCount c.edges (2^S.levelBits c.depth) := by
  rw [Nat.card_prod,Nat.card_fin,Nat.card_fin]

omit [Fintype Mode] [DecidableEq Mode] in
/-- The table positions name distinct actual source address pairs when
the chosen centres are distinct. A streaming implementation may avoid
keeping the whole table, but is still specified to acquire those values. -/
theorem fallback_table_addresses (S : Shape Host Mode) (c : Call Host) (m : ℕ)
    (centers : Fin (m+1) ↪ Center S c) :
    Function.Injective (fun a : Fin (m+1) × Probe S c => (centers a.1,a.2)) := by
  intro a b h
  have hsecond := congrArg Prod.snd h
  exact Prod.ext (centers.injective (congrArg Prod.fst h)) hsecond

#print axioms runtime_replies_exact
#print axioms runtime_local_exact
#print axioms runtime_zero_exact
#print axioms fallback_table_cells
#print axioms fallback_table_addresses
end J6R12Repack
