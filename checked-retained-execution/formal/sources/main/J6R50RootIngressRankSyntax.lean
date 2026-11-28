import J6R50RootIngressRankChart

/-! The selected chart must still supply raw half ranks and raw row
labels for its chosen old equality-tree ordering. It need not supply
clause selectors: those are generated from the actual guarded syntax's
literal list order. Equality rows have no original clause selector. -/
namespace J6R50RootIngress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime J6R49RootIngress J6R30GeneratedRootLayout
open J6OrientedHost J7R10Ports J7R10Plant
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6800000

structure BareRankRow (w r : ℕ) where
  label : Word r
  ranks : List (Word w)

def roleRows {w r h : ℕ} (guard : BitsCNF) (lit eqs : List (BareRankRow w r)) :
    Meter (List (RowBook w r h)) :=
  let tape := indexTape h guard.length
  let clauseRows := lit.zipWith (fun a j => (⟨a.label,some j,a.ranks⟩ : RowBook w r h)) tape.result
  let equalRows := eqs.map (fun a => (⟨a.label,none,a.ranks⟩ : RowBook w r h))
  ⟨clauseRows++equalRows,tape.steps+9+lit.length*(9+4*(r+h))+eqs.length*(8+4*r)⟩

theorem role_row_fee {w r h : ℕ} (guard : BitsCNF) (lit eqs : List (BareRankRow w r))
    (hh : 0<h) (hclip : guard.length≤2^h) :
    (roleRows (h:=h) guard lit eqs).steps≤
      tapeFee h guard.length+9+lit.length*(9+4*(r+h))+eqs.length*(8+4*r) := by
  have H := (index_tape_exact h guard.length hh hclip).2
  dsimp only [roleRows]
  omega

variable {V : Type} [DecidableEq V] [Fintype V]
variable (H : CNF V)
variable {w r c d h : ℕ}
variable (C : LiteralCodec (physicalPlant H) r c d)

noncomputable def bareRankSpec (v : Old H) : BareRankRow w r :=
  let R := rowSpec (h:=0) H C v
  ⟨R.label,R.ranks⟩

def oldOrder (eqOrder : List (TreeIndex H)) : List (Old H) :=
  List.ofFn (fun i : J7R9Compiler.ClauseIndex H => Sum.inl i)++eqOrder.map Sum.inr

theorem oldOrder_exhaustive (eqOrder : List (TreeIndex H)) (ex : ∀ i,i∈eqOrder) :
    ∀ v : Old H,v∈oldOrder H eqOrder := by
  intro v
  cases v with
  | inl i => exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  | inr j => exact List.mem_append_right _ (List.mem_map_of_mem (ex j))

theorem role_rows_exact (code : V→List Bool) (hh : 0<h) (hclip : H.length≤2^h)
    (eqOrder : List (TreeIndex H))
    (lit eqs : List (BareRankRow w r))
    (hl : lit=List.ofFn (fun i : J7R9Compiler.ClauseIndex H => bareRankSpec H C (.inl i)))
    (he : eqs=eqOrder.map (fun i => bareRankSpec H C (.inr i))) :
    (roleRows (h:=h) (codeCNF code H) lit eqs).result =
      (oldOrder H eqOrder).map (rowSpec H C) := by
  subst lit eqs
  have tape : (indexTape h (codeCNF code H).length).result=
      List.ofFn (fun i : Fin H.length => wordAt h i.val) := by
    change (indexTape h (H.map _).length).result=_
    rw [List.length_map]
    exact (index_tape_exact h H.length hh hclip).1
  simp only [roleRows,tape,zip_ofFn_exact,oldOrder,List.map_append,List.map_ofFn,List.map_map,Function.comp_def]
  rfl

def compileParsedRoles {w r c d h : ℕ}
    (n : ℕ) (declares : List (List Bool)) (raw : BitsCNF)
    (lit eqs : List (BareRankRow w r)) (cols : ColBook w) :
    Meter (Option (List (SignedHalfPort r c d))) :=
  let G := guardedMeter declares raw
  let B := roleRows (h:=h) G.result lit eqs
  let A := recoveredAtlas (c:=c) (d:=d) n B.result cols
  match A.result with
  | none => ⟨none,G.steps+B.steps+A.steps+7⟩
  | some pos =>
    let Y := signAtlas G.result pos
    ⟨Y.result,G.steps+B.steps+A.steps+Y.steps+8⟩

theorem paid_original_compact_from_categorized_ranks (F : CNF V)
    (code : V→List Bool) (inj : Function.Injective code)
    (C : LiteralCodec (physicalPlant (guarded F)) r c d)
    (hw : 0<w) (hd : 0<d) (hc : 0<c) (hh : 0<h)
    (rankFit : nWires (guarded F)≤2^w) (clauseFit : (guarded F).length≤2^h)
    (lit eqs : List (BareRankRow w r)) (cols : ColBook w)
    (eqOrder : List (TreeIndex (guarded F))) (ex : ∀ j,j∈eqOrder)
    (hl : lit=List.ofFn (fun i : J7R9Compiler.ClauseIndex (guarded F) =>
      bareRankSpec (guarded F) C (.inl i)))
    (he : eqs=eqOrder.map (fun i => bareRankSpec (guarded F) C (.inr i)))
    (exactCol : cols=colSpec (guarded F)) :
    let run := compileParsedRoles (c:=c) (d:=d) (h:=h) (nWires (guarded F))
      ((Finset.univ : Finset V).toList.map code) (codeCNF code F) lit eqs cols
    ∃ out : CNFPortFile F r c d,run.result=some out.raw ∧ out.codec=C := by
  let Y := (guardedMeter ((Finset.univ : Finset V).toList.map code) (codeCNF code F)).result
  have gy : Y=codeCNF (guardCode code) (guarded F) := paid_guard_original_syntax code inj F
  have hr : (roleRows (h:=h) Y lit eqs).result=(oldOrder (guarded F) eqOrder).map (rowSpec (guarded F) C) := by
    rw [gy]
    exact role_rows_exact (guarded F) C (guardCode code) hh clauseFit eqOrder lit eqs hl he
  have a := recovered_actual_unsigned_atlas (guarded F) C hw rankFit hd hc
    (roleRows (h:=h) Y lit eqs).result cols (oldOrder (guarded F) eqOrder)
    (oldOrder_exhaustive (guarded F) eqOrder ex) hr exactCol
  let raw := List.ofFn (plantHalfPort (physicalPlant (guarded F)) C)
  refine ⟨⟨C,raw,rfl⟩,?_,rfl⟩
  dsimp only [compileParsedRoles]
  change (match (recoveredAtlas (c:=c) (d:=d) (nWires (guarded F)) (roleRows (h:=h) Y lit eqs).result cols).result with
    | none => (⟨none,_⟩ : Meter (Option (List (SignedHalfPort r c d))))
    | some pos => ⟨(signAtlas Y pos).result,_⟩).result = some raw
  rw [a]
  change (signAtlas Y (List.ofFn (positionForWire (guarded F) C :
    Fin (nWires (guarded F))→Position r c d h))).result = some raw
  rw [gy]
  exact exact_compact_chart_rows (guarded F) (guardCode code) C clauseFit _ rfl

#print axioms role_row_fee
#print axioms oldOrder_exhaustive
#print axioms role_rows_exact
#print axioms paid_original_compact_from_categorized_ranks
end J6R50RootIngress
