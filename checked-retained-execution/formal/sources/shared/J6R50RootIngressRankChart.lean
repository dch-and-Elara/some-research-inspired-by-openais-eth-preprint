import J6R50RootIngressRankCore
import J6R49RootIngressAssembly

/-! Bind the separate raw rank books to the actual chosen chart. These
are wire data from two gate lists, not independently supplied final
positions, and transport through the old bijections is literal. -/
namespace J6R50RootIngress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6R49RootIngress J6R30GeneratedRootLayout J6OrientedHost J7R10Ports J7R10Plant
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 9300000
set_option maxRecDepth 2500

theorem zip_ofFn_exact {I A B : Type*} (n : ℕ) (a : Fin n→I) (b : Fin n→A) (f : I→A→B) :
    (List.ofFn a).zipWith f (List.ofFn b)=List.ofFn (fun i => f (a i) (b i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ]
    simp only [List.zipWith_cons_cons]
    rw [ih]

theorem wordAt_rank_inj {w x y : ℕ} (hx : x<2^w) (hy : y<2^w)
    (e : wordAt w x=wordAt w y) : x=y := by
  have h := congrArg (fun z : Word w => bitsValue z.val) e
  change bitsValue (encodeBits w x)=bitsValue (encodeBits w y) at h
  rwa [encodeBits_exact _ _ hx,encodeBits_exact _ _ hy] at h

variable {V : Type} [DecidableEq V] [Fintype V]
variable (H : CNF V)
variable {w r c d h : ℕ}
variable (C : LiteralCodec (physicalPlant H) r c d)

def clauseKey (v : Old H) : Option (Word h) :=
  match v with | .inl i => some (wordAt h i.val) | .inr _ => none

noncomputable def rowRank (x : OldPort H) : Word w :=
  wordAt w ((physicalPlant H).rowPort x).val

noncomputable def colRank (j : Fin (nSubdiv H)) (b : Bool) : Word w :=
  wordAt w ((physicalPlant H).colPort (j,b)).val

noncomputable def rowSpec (v : Old H) : RowBook w r h :=
  ⟨C.rowCode v,clauseKey H v,List.ofFn (fun j : Fin (J7R10Ports.degree H v) => rowRank H ⟨v,j⟩)⟩

noncomputable def colSpec : ColBook w :=
  List.ofFn (fun j : Fin (nSubdiv H) => (colRank H j false,colRank H j true))

noncomputable def rowRec (x : OldPort H) : Word w × RowHit r d h :=
  (rowRank H x,C.rowCode x.1,wordAt d x.2.val,clauseKey H x.1)

noncomputable def colRec (y : Fin (nSubdiv H) × Bool) : Word w × ColHit c :=
  (colRank H y.1 y.2,wordAt c y.1.val,y.2)

theorem emit_rows_physical (hd : 0<d) (order : List (Old H)) :
    (emitRows (d:=d) (order.map (rowSpec H C : Old H→RowBook w r h))).result =
      order.flatMap (fun v => List.ofFn (fun j : Fin (J7R10Ports.degree H v) =>
        rowRec H C ⟨v,j⟩)) := by
  induction order with
  | nil => rfl
  | cons v vs ih =>
    have fit : J7R10Ports.degree H v≤2^d := C.portFit v
    have tape := (index_tape_exact d (J7R10Ports.degree H v) hd fit).1
    simp only [List.map_cons,emitRows,rowSpec,List.length_ofFn,List.flatMap_cons,tape,ih]
    rw [zip_ofFn_exact]
    rfl

theorem emit_cols_physical (hc : 0<c) (fit : nSubdiv H≤2^c) :
    (emitColumns (c:=c) (colSpec H : ColBook w)).result =
      (List.ofFn (fun j : Fin (nSubdiv H)=>[colRec H (j,false),colRec H (j,true)])).flatten := by
  have tape := (index_tape_exact c (nSubdiv H) hc fit).1
  simp only [emitColumns,colSpec,List.length_ofFn,tape,zip_ofFn_exact]
  rfl

theorem row_hit_exact (hw : nWires H≤2^w) (hd : 0<d)
    (order : List (Old H)) (exhaustive : ∀ v : Old H,v∈order) (u : Fin (nWires H)) :
    let p := (positionForWire H C u : Position r c d h)
    (findRank (wordAt w u.val) (emitRows (d:=d) (order.map (rowSpec H C))).result).result =
      some (p.row,p.leg,p.clause) := by
  rw [emit_rows_physical H C hd order]
  let x := (physicalPlant H).rowPort.symm u
  have ex : (physicalPlant H).rowPort x=u := (physicalPlant H).rowPort.apply_symm_apply u
  have hx : rowRec H C x=(wordAt w u.val,(positionForWire H C u : Position r c d h).row,
      (positionForWire H C u : Position r c d h).leg,
      (positionForWire H C u : Position r c d h).clause) := by
    change (wordAt w ((physicalPlant H).rowPort x).val,_,_,_)=_
    rw [ex]
    rfl
  apply find_rank_exact
  · rw [← hx]
    exact List.mem_flatMap.mpr ⟨x.1,exhaustive _,List.mem_ofFn.mpr ⟨x.2,rfl⟩⟩
  · intro a ha
    obtain ⟨v,_,hr⟩ := List.mem_flatMap.mp ha
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hr
    have er : ((physicalPlant H).rowPort ⟨v,j⟩).val=u.val :=
      wordAt_rank_inj (((physicalPlant H).rowPort ⟨v,j⟩).isLt.trans_le hw)
        (u.isLt.trans_le hw) (congrArg Prod.fst hj)
    have r : (⟨v,j⟩ : OldPort H)=x :=
      (physicalPlant H).rowPort.injective ((Fin.ext er).trans ex.symm)
    rw [show rowRec H C ⟨v,j⟩=rowRec H C x from congrArg (rowRec H C) r,hx] at hj
    exact (congrArg Prod.snd hj).symm

theorem col_hit_exact (hw : nWires H≤2^w) (hc : 0<c) (u : Fin (nWires H)) :
    let p := (positionForWire H C u : Position r c d h)
    (findRank (wordAt w u.val) (emitColumns (c:=c) (colSpec H)).result).result =
      some (p.column,p.side) := by
  rw [emit_cols_physical H hc C.columnFit]
  let y := (physicalPlant H).colPort.symm u
  have ey : (physicalPlant H).colPort y=u := (physicalPlant H).colPort.apply_symm_apply u
  have hy : colRec (w:=w) (c:=c) H y=(wordAt w u.val,
      (positionForWire H C u : Position r c d h).column,
      (positionForWire H C u : Position r c d h).side) := by
    change (wordAt w ((physicalPlant H).colPort y).val,_,_)=_
    rw [ey]
    rfl
  apply find_rank_exact
  · rw [←hy]
    apply List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨y.1,rfl⟩,?_⟩
    cases hyb : y.2
    · exact List.mem_cons.mpr (Or.inl (congrArg (fun b => colRec (w:=w) (c:=c) H (y.1,b)) hyb))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
        (Or.inl (congrArg (fun b => colRec (w:=w) (c:=c) H (y.1,b)) hyb))))
  · intro a ha
    obtain ⟨l,hl,hm⟩ := List.mem_flatten.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hl
    have witness : ∃ b, colRec (w:=w) (c:=c) H (j,b)=(wordAt w u.val,a) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      exact hm.elim (fun h => ⟨false,h.symm⟩) (fun h => ⟨true,h.symm⟩)
    obtain ⟨b,hj⟩ := witness
    have er : ((physicalPlant H).colPort (j,b)).val=u.val :=
      wordAt_rank_inj (((physicalPlant H).colPort (j,b)).isLt.trans_le hw)
        (u.isLt.trans_le hw) (congrArg Prod.fst hj)
    have rr : (j,b)=y :=
      (physicalPlant H).colPort.injective ((Fin.ext er).trans ey.symm)
    rw [show colRec (w:=w) (c:=c) H (j,b)=colRec H y from congrArg (colRec H) rr,hy] at hj
    exact (congrArg Prod.snd hj).symm

theorem recovered_actual_unsigned_atlas
    (hw : 0<w) (fitw : nWires H≤2^w) (hd : 0<d) (hc : 0<c)
    (row : List (RowBook w r h)) (col : ColBook w)
    (order : List (Old H)) (exhaustive : ∀ v : Old H,v∈order)
    (exactRow : row=order.map (rowSpec H C)) (exactCol : col=colSpec H) :
    (recoveredAtlas (c:=c) (d:=d) (nWires H) row col).result=
      some (List.ofFn (positionForWire H C : Fin (nWires H)→Position r c d h)) := by
  subst row col
  simp only [recoveredAtlas,(index_tape_exact w (nWires H) hw fitw).1]
  have D := joined_keys_exact
    (emitRows (d:=d) (order.map (rowSpec H C))).result
    (emitColumns (c:=c) (colSpec H : ColBook w)).result
    (List.ofFn (fun u : Fin (nWires H)=>u))
    (fun u => wordAt w u.val) (positionForWire H C : Fin (nWires H)→Position r c d h)
    (row_hit_exact H C fitw hd order exhaustive) (col_hit_exact H C fitw hc)
  simpa only [List.map_ofFn] using D

#print axioms zip_ofFn_exact
#print axioms wordAt_rank_inj
#print axioms emit_rows_physical
#print axioms emit_cols_physical
#print axioms row_hit_exact
#print axioms col_hit_exact
#print axioms recovered_actual_unsigned_atlas
end J6R50RootIngress
