import J6R62LeafTerminal
import J6R58LeafScaleArithmetic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 35000000
set_option maxRecDepth 4400

/-! Census of all actual owner rows and fresh atlas columns. Isolates
are counted: an edge-incidence bound alone would be false. -/
namespace J6R62Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
open J6R48Leaf J6R57Public J6R58LeafScale

theorem accepted_gather_census {A D : Type*} (s : ℕ) (f : A → Meter (Option D))
    (xs : List A) : ∀ out, (gatherOptions s f xs).result=some out → out.length=xs.length := by
  induction xs with
  | nil =>
    intro out h
    obtain rfl := Option.some.inj h
    rfl
  | cons x xs ih =>
    intro out h
    dsimp only [gatherOptions] at h
    cases hz : (f x).result with
    | none => rw [hz] at h; contradiction
    | some ready =>
      rw [hz] at h
      dsimp only [Option.bind] at h
      cases he : (gatherOptions s f xs).result with
      | none => rw [he] at h; contradiction
      | some rs =>
        simp only [he,Option.map_some,Option.some.injEq] at h
        subst out
        simp only [List.length_cons,ih rs he]

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))

theorem actual_selected_owner_count (A : OwnerTerminalInput X p w Y) :
    (selectOwnerKeys (word (p.ticket w).groupAt.val) A.headers.raw).result.length=
      Nat.card (p.ticket w).child.host.Row := by
  let O := (readOldVertices Y.site A.headers).result
  have eq := (exact_old_vertices_from_grouped_headers Y.site A.headers).1.symm.trans O.exact
  change (selectOwnerKeys (word (p.ticket w).groupAt.val) A.headers.raw).result=
    O.rows.map (nativeRowKey Y.site) at eq
  rw [eq,List.length_map]
  exact actual_complete_order_length O.rows O.unique O.all

theorem actual_current_atlas_column_count :
    (trueFreshPages Y).length=Nat.card (p.ticket w).child.host.Col := by
  have eq := cols_of_birth_complete (T:=T) (v:=p.ticket w)
  have n := actual_complete_order_length _ eq.1 eq.2
  change ((trueFreshPages Y).map (physicalChildCols (T:=T) (v:=p.ticket w)).symm).length=_ at n
  simpa only [List.length_map] using n

theorem actual_terminal_census_and_native_width
    (A : OwnerTerminalInput X p w Y)
    (older : List (ReadCmd key (pageKeyWidth m+pad)))
    (hit : (oldCompiler X p w Y A).result=some older) :
    let r := exteriorChild G ell X.centre X.sample X.group
    let F := T.frame (Path.step p w).reached
    let cmds := older++(trueFreshPages Y).map (freshWord Y)
    older.length=Nat.card (p.ticket w).child.host.Row ∧
      cmds.length=vertexCount (p.ticket w).child.host ∧
      cmds.length≤vertexCount r.host+4*(C*s) ∧
      F.words.length=4*Nat.clog 2 s ∧ (p.ticket w).child.prec≤r.prec+160*C*s^2 := by
  let book := cachedBook Y A.saved
  let chosen := selectOwnerKeys (word (p.ticket w).groupAt.val) A.headers.raw
  let command := compileByRoster (p.ticket w).child.edges book.result A.saved.rows A.roster.raw
  change (gatherOptions 1 command chosen.result).result=some older at hit
  have oldN := (accepted_gather_census 1 command chosen.result older hit).trans
    (actual_selected_owner_count X p w Y A)
  have cmdN : (older++(trueFreshPages Y).map (freshWord Y)).length=vertexCount (p.ticket w).child.host := by
    rw [List.length_append,List.length_map,oldN,actual_current_atlas_column_count X p w Y]
    rfl
  have hw := actual_leaf_field_width_and_vertices (T:=T) (Path.step p w)
  exact ⟨oldN,cmdN,cmdN.trans_le hw.2.2,hw.1,hw.2.1⟩

#print axioms accepted_gather_census
#print axioms actual_selected_owner_count
#print axioms actual_current_atlas_column_count
#print axioms actual_terminal_census_and_native_width
end
end J6R62Leaf
