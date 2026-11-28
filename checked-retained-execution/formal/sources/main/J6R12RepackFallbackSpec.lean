import J6R12RepackFallbackMesh

/-! The very same acquired binary table meets the direct source
specification of the typed physical factory. This interface lets the
closed source theorem certify the fallback without introducing a second
layout, a genuine zero node, or a separately assumed child oracle. -/
namespace J6R12Repack
open scoped Polynomial BigOperators
open Polynomial J6ActiveRun J6R9Recursive J6ActiveSchedule J6ActiveUniqueness
open J6ActivePrintedHermite J6R11Integral J6Mesh

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {S : Shape Host Mode} {f : ℤ[X]} {ell : ℕ} {B : Blueprint S f ell}
variable {c : Call Host}

theorem spec_runtime_replies_exact (D : B.SourceSpec)
    (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hc : D.Valid c) (ha : S.cutoff < c.edges) :
    runtimeReplies B c = (fun w => B.expect (B.program.child c w)) := by
  funext w
  exact B.run_exact D hf hd (B.program.child c w) (D.child_valid c hc ha w)

set_option maxHeartbeats 2100000 in
theorem spec_runtime_local_exact (D : B.SourceSpec)
    (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hc : D.Valid c) (ha : S.cutoff < c.edges) (t : Center S c) :
    decodedAt S f ell c (D.fit c hc ha) (runtimeReplies B c) t =
      (D.jets c t.val).map (reduce (registerPrecision S c t) f ell) := by
  rw [spec_runtime_replies_exact D hf hd hc ha]
  have hp : 0 < registerPrecision S c t :=
    (Nat.zero_le c.prec).trans_lt (child_monotone _ _ _ _ _ (Nat.zero_lt_of_lt ha))
  have hD : (D.jets c t.val).natDegree ≤
      J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth) := by
    rw [← natDegree_map_eq_of_injective (embed_inj f hf ell), D.integral c hc ha t]
    exact (atNode_degree _ _ _).trans (D.degree c hc ha)
  exact decodedAt_exact S f hf hd ell c (D.fit c hc ha) _ t hp _
    (natDegree_map_le.trans hD) (D.grouped c hc ha t)

noncomputable def specMeshFallback (D : B.SourceSpec) (hc : D.Valid c) (ha : S.cutoff<c.edges)
    (m native : ℕ) (hn : native≤m) (mesh : MeshAt S c m) (j : Fin (m+1)) :
    Box f ell (registerPrecision S c (meshCenters m native hn mesh j)) :=
  (J6ActiveInterpolation.decoded (sampleNode S f ell c (D.fit c hc ha) (meshCenters m native hn mesh j))
    (meshTable B c m native hn mesh j)).eval 0

theorem spec_mesh_fallback_correct (D : B.SourceSpec)
    (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hc : D.Valid c) (ha : S.cutoff<c.edges)
    (m native : ℕ) (hn : native≤m) (mesh : MeshAt S c m) (j : Fin (m+1)) :
    specMeshFallback D hc ha m native hn mesh j =
      reduce (registerPrecision S c (meshCenters m native hn mesh j)) f ell
        ((D.jets c (index m j : ℤ)).coeff 0) := by
  change (decodedAt S f ell c (D.fit c hc ha) (runtimeReplies B c)
    (meshCenters m native hn mesh j)).eval 0 = _
  rw [spec_runtime_local_exact D hf hd hc ha, ← coeff_zero_eq_eval_zero,coeff_map]
  rfl

#print axioms spec_runtime_replies_exact
#print axioms spec_runtime_local_exact
#print axioms specMeshFallback
#print axioms spec_mesh_fallback_correct
end J6R12Repack
