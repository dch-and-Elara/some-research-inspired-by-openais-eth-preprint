
import J6R32RootGeneratedRegistryInputsHalfTape
import J6R32RootGeneratedRegistryInputsSite

/-! Attach the proof-side PhysicalPorts view to the *made* R31-derived
two-side tape. Actual consumers only read its raw bytes. All input
port groups refer to the true stable root Ready/centre, not to a
postulated independent graph or any child selector. -/
namespace J6R32RootGeneratedRegistryInputs
open scoped Polynomial Classical
open Polynomial AOracleMachineTime
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R25PreparedSupply
open J6R12Repack J6R11Repack J6R12Blueprint J6ActiveRun J6ActiveSchedule J1PPrinted
open J6R11Blueprint J6R10Repack J6R15ModeCost J6R27OriginalGate J6R9PacketScopes
open J6R24LegalLayout J6R26StablePreparedRoot J6Mesh J6OrientedHost P11FullPacking
set_option maxHeartbeats 13000000
set_option maxRecDepth 2250

theorem retained_group_transport {E A B : Type} {N : Network E A B} {a b : ℕ}
    (e : a=b) (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (j : Fin b)
    (axis : j.val=i.val) (side : Port E) :
    retainedGroup N (atGroup (cast (congrArg (fun k=>PhysicalPacking N k (Fin 64)) e) P) j) side =
      retainedGroup N (atGroup P i) side := by
  subst b
  have H : j=i := Fin.ext axis
  subst j
  rfl

theorem half_row_groups {V : Type} [Fintype V] {m n : ℕ} (T : Plant V m n)
    (i : Fin (a m)) (p : Port (RootWire m)) :
    (expectedHalfRow T i p).group.val=
      (retainedGroup (rootNetwork (b:=K m) (l:=printedHalf m) T (J6R28GeneratedRootFrame.constantRootWord m))
        (atGroup (rootChart T) i) p).val := by
  let P := rootChart T
  cases p with
  | inl e =>
    let g := rowGroup P.mask i (P.seat e)
    change (word (q:=6) g.val).val=(atGroup P i (.inl ((rootNetwork (b:=K m)
      (l:=printedHalf m) T (J6R28GeneratedRootFrame.constantRootWord m)).row e))).val
    rw [word_val g.isLt]
    exact congrArg Fin.val (row_symbol P i e)
  | inr e =>
    let g := colGroup P.mask i (P.seat e)
    change (word (q:=6) g.val).val=(atGroup P i (.inr ((rootNetwork (b:=K m)
      (l:=printedHalf m) T (J6R28GeneratedRootFrame.constantRootWord m)).col e))).val
    rw [word_val g.isLt]
    exact congrArg Fin.val (col_symbol P i e)

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (J6R28GeneratedRootFrame.constantRootWord m))

theorem root_half_groups_actual (ell : ℕ) (i : J6Recovery.Addr m) (p : Port (RootWire m)) :
    (expectedHalfRow T (oddAxis m) p).group.val=
      (physicalGroup (G.selector ell) (G.ready ell) (G.centre ell i) p).val := by
  let root := physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m)
  letI := root.host.finiteEdge
  letI := root.host.finiteRow
  letI := root.host.finiteCol
  let N := root.host.network
  let j := centerIndex (G.ready ell) (G.centre ell i)
  have A := odd_site_matches_geometry G ell i
  refine (half_row_groups T (oddAxis m) p).trans ?_
  change (retainedGroup N (atGroup (rootChart T) (oddAxis m)) p).val =
    (retainedGroup N (atGroup (packing (G.selector ell) (G.ready ell)) j) p).val
  rw [A.1]
  exact (congrArg Fin.val (retained_group_transport (mesh_root_bits m native G.nativeFits).symm
    (rootChart T) (oddAxis m) j A.2.1 p)).symm

noncomputable def makeTypedRootParent {r c d : ℕ} (source : LiteralPortFile T r c d)
    (ell : ℕ) (center : J6Recovery.Addr m) : Meter (rootParentFile G ell center (rootHalfWidth m)) :=
  let H := makeHalfTape m [] source.raw
  let words := actual_root_half_tape source (oddAxis m) [] rfl
  let all := root_half_order_complete m
  ⟨⟨H.result,rootHalfOrder m,all.1,all.2.1,expectedHalfRow T (oddAxis m),words.1,
    root_half_groups_actual G ell center,half_addresses_unique T (oddAxis m)⟩,H.steps⟩

theorem generated_typed_parent_receipt {r c d : ℕ} (source : LiteralPortFile T r c d)
    (ell : ℕ) (center : J6Recovery.Addr m) :
    let H := makeTypedRootParent G source ell center
    H.result.raw=(makeHalfTape m [] source.raw).result ∧
      H.result.raw.length=2*M m ∧ H.steps≤halfTapeFee m r c d := by
  have Q := actual_root_half_tape source (oddAxis m) [] rfl
  exact ⟨rfl,Q.2.1,Q.2.2⟩

#print axioms retained_group_transport
#print axioms root_half_groups_actual
#print axioms generated_typed_parent_receipt
end J6R32RootGeneratedRegistryInputs
