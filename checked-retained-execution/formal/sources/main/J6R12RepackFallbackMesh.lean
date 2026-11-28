import J6R12RepackRootProbe
import J6R12RepackFallback

/-! The J6 fallback formed from the actual root program's child replies.
It uses all printed binary probes at every designated odd centre and
extracts its zero value by interpolation, not by a free zero register. -/
namespace J6R12Repack
open scoped Polynomial BigOperators Classical
open Polynomial J6Mesh J6ActiveRun J6R9Recursive J6ActiveSchedule J6R11Integral

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {S : Shape Host Mode} {f : ℤ[X]} {ell : ℕ} {B : Blueprint S f ell}
variable {c : Call Host}

structure MeshAt (S : Shape Host Mode) (c : Call Host) (m : ℕ) : Prop where
  edges : c.edges=M m
  width : S.levelWidth c.depth=u m
  bits : S.levelBits c.depth=a m

/-- Retype an actual odd centre for the solver's own mode shape. Only its
retained order metadata matter, not the ambient indexing of modes. -/
def meshCenters (m native : ℕ) (hn : native≤m) (mesh : MeshAt S c m) :
    Fin (m+1) ↪ Center S c where
  toFun j := ⟨(index m j : ℤ),by
    rw [mesh.bits,mesh.edges,mesh.width]
    simpa only [mesh_root_bits m native hn,mesh_root_width m native hn] using
      odd_root_active m native hn j⟩
  inj' := by
    intro i j h
    have he := congrArg Subtype.val h
    change (index m i:ℤ)=(index m j:ℤ) at he
    have he' : index m i=index m j := by exact_mod_cast he
    apply Fin.ext
    unfold index at he'
    omega

omit [Fintype Mode] [DecidableEq Mode] in
theorem mesh_receiving_precision (m native : ℕ) (hn : native≤m) (mesh : MeshAt S c m)
    (j : Fin (m+1)) :
    registerPrecision S c (meshCenters m native hn mesh j) = J6SourcePrecision.printed m c.prec := by
  change childPrecision c.prec (S.levelBits c.depth) c.edges (S.levelWidth c.depth) (index m j : ℤ) = _
  rw [mesh.bits,mesh.width,mesh.edges]
  unfold childPrecision
  rw [(J6RecursiveCrossing.odd_center_valuation m j).2.1,pow_zero,Nat.div_one]
  rfl

/-- The acquired table's entries are sums/products of the actual results
of all the generated children for the designated pair (centre,probe). -/
noncomputable def meshTable (B : Blueprint S f ell) (c : Call Host)
    (m native : ℕ) (hn : native≤m) (mesh : MeshAt S c m) :
    ∀ j : Fin (m+1), Probe S c → Box f ell (registerPrecision S c (meshCenters m native hn mesh j)) :=
  fun j z => groupedSample S f ell c (runtimeReplies B c) (meshCenters m native hn mesh j) z

noncomputable def meshFallback (D : FrozenLayout B) (hc : D.Valid c) (ha : S.cutoff<c.edges)
    (m native : ℕ) (hn : native≤m) (mesh : MeshAt S c m) (j : Fin (m+1)) :
    Box f ell (registerPrecision S c (meshCenters m native hn mesh j)) :=
  (J6ActiveInterpolation.decoded (sampleNode S f ell c (D.fit c hc ha) (meshCenters m native hn mesh j))
    (meshTable B c m native hn mesh j)).eval 0

theorem mesh_fallback_correct (D : FrozenLayout B) (grouped : D.ExactGrouped)
    (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hc : D.Valid c) (ha : S.cutoff<c.edges)
    (m native : ℕ) (hn : native≤m) (mesh : MeshAt S c m) (j : Fin (m+1)) :
    meshFallback D hc ha m native hn mesh j =
      reduce (registerPrecision S c (meshCenters m native hn mesh j)) f ell
        (((D.active c hc ha).jet (index m j:ℤ)).coeff 0) :=
  runtime_zero_exact D grouped hf hd c hc ha (meshCenters m native hn mesh j)

omit [Fintype Mode] [DecidableEq Mode] in
theorem mesh_table_acquisition (m : ℕ) (mesh : MeshAt S c m) :
    Nat.card (Fin (m+1) × Probe S c) = (m+1)*(M m*(2*L m-1)+1) := by
  rw [fallback_table_cells S c m,mesh.edges,mesh.bits]
  rfl

#print axioms meshCenters
#print axioms mesh_receiving_precision
#print axioms mesh_fallback_correct
#print axioms mesh_table_acquisition
end J6R12Repack
