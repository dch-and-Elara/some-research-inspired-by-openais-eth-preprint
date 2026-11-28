import J6R50RootIngressRankChart
import J6R49RootIngressFees

/-! Charge the actual generated rank, column, and leg words, both
resident book scans per output, and the earlier CNF ingress pass. -/
namespace J6R50RootIngress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime J6R49RootIngress
open J6R30GeneratedRootLayout J6OrientedHost J7R10Plant J7R10Ports
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

def rowCount {w r h : ℕ} (rows : List (RowBook w r h)) : ℕ :=
  (rows.map (fun s => s.ranks.length)).sum

def rowBookFee {w r h : ℕ} (d : ℕ) (rows : List (RowBook w r h)) : ℕ :=
  1+(rows.map (fun s =>
    tapeFee d s.ranks.length+8+s.ranks.length*(16+4*(w+r+d+h)))).sum

def colBookFee (w c n : ℕ) : ℕ := tapeFee c n+7+n*(28+8*(w+c))

theorem emitted_rows_billed {w r d h : ℕ} (rows : List (RowBook w r h))
    (hd : 0<d) (fit : ∀ s∈rows, s.ranks.length≤2^d) :
    (emitRows (d:=d) rows).result.length=rowCount rows ∧
      (emitRows (d:=d) rows).steps≤rowBookFee d rows := by
  induction rows with
  | nil => simp [emitRows,rowCount,rowBookFee]
  | cons a as ih =>
    obtain ⟨te,tc⟩ := index_tape_exact d a.ranks.length hd (fit a List.mem_cons_self)
    obtain ⟨le,lc⟩ := ih (fun s hs => fit s (List.mem_cons_of_mem _ hs))
    simp only [emitRows,List.length_zipWith,List.length_append,te,List.length_ofFn,min_self,le,
      rowCount,rowBookFee,List.map_cons,List.sum_cons]
    constructor
    · trivial
    · unfold rowBookFee at lc
      omega

theorem flatten_pair_chunk_length {A : Type*} (ys : List (List A))
    (h : ∀ l∈ys,l.length=2) : ys.flatten.length=2*ys.length := by
  induction ys with
  | nil => simp
  | cons a as ih =>
    have q := h _ List.mem_cons_self
    have e := ih (fun l hl => h l (List.mem_cons_of_mem _ hl))
    simp only [List.flatten_cons,List.length_append,List.length_cons,q,e]
    omega

theorem zip_columns_constant_width {w c : ℕ} (col : ColBook w) (codes : List (Word c)) :
    ∀ y∈col.zipWith colData codes,y.length=2 := by
  induction col generalizing codes with
  | nil => simp
  | cons a as ih =>
    cases codes with
    | nil => simp
    | cons k ks =>
      intro y hy
      rcases List.mem_cons.mp hy with eq|tail
      · subst y
        rfl
      · exact ih ks y tail

theorem emitted_columns_billed {w c : ℕ} (col : ColBook w)
    (hc : 0<c) (fit : col.length≤2^c) :
    (emitColumns (c:=c) col).result.length=2*col.length ∧
      (emitColumns (c:=c) col).steps≤colBookFee w c col.length := by
  obtain ⟨te,tc⟩ := index_tape_exact c col.length hc fit
  constructor
  · dsimp only [emitColumns]
    rw [show (indexTape c col.length).result=List.ofFn (fun i : Fin col.length => wordAt c i.val) from te]
    rw [flatten_pair_chunk_length, List.length_zipWith,List.length_ofFn,min_self]
    exact zip_columns_constant_width col _
  · dsimp only [emitColumns,colBookFee]
    exact Nat.add_le_add_right (Nat.add_le_add_right tc 7) _

def recoveredFee {w r h : ℕ} (c d n : ℕ) (rows : List (RowBook w r h)) (cols : ColBook w) : ℕ :=
  rowBookFee d rows+colBookFee w c cols.length+tapeFee w n+
    (1+n*(positionFee w r c d h (rowCount rows) (2*cols.length)+4))+8

theorem recovered_atlas_fee {w r c d h : ℕ} (n : ℕ) (rows : List (RowBook w r h)) (cols : ColBook w)
    (hw : 0<w) (hd : 0<d) (hc : 0<c) (fitw : n≤2^w)
    (fitd : ∀ s∈rows,s.ranks.length≤2^d) (fitc : cols.length≤2^c) :
    (recoveredAtlas (c:=c) (d:=d) n rows cols).steps≤recoveredFee c d n rows cols := by
  obtain ⟨rl,rc⟩ := emitted_rows_billed (d:=d) rows hd fitd
  obtain ⟨cl,cc⟩ := emitted_columns_billed (c:=c) cols hc fitc
  obtain ⟨kl,kc⟩ := index_tape_exact w n hw fitw
  have jl : (indexTape w n).result.length=n := by rw [kl,List.length_ofFn]
  have j := joined_keys_fee (emitRows (d:=d) rows).result (emitColumns (c:=c) cols).result
    (indexTape w n).result
  rw [rl,cl,jl] at j
  dsimp only [recoveredAtlas,recoveredFee]
  omega

def compileFromBooks {w r c d h : ℕ} (n : ℕ) (keys : List (List Bool)) (raw : BitsCNF)
    (rows : List (RowBook w r h)) (cols : ColBook w) :
    Meter (Option (List (SignedHalfPort r c d))) :=
  let A := recoveredAtlas (c:=c) (d:=d) n rows cols
  match A.result with
  | none => ⟨none,A.steps+4⟩
  | some pos =>
    let P := compileRootIngress keys raw pos
    ⟨P.result,A.steps+P.steps+6⟩

variable {V : Type} [DecidableEq V] [Fintype V]

theorem paid_original_compact_from_books (F : CNF V)
    (code : V→List Bool) (inj : Function.Injective code) {w r c d h : ℕ}
    (C : LiteralCodec (physicalPlant (guarded F)) r c d)
    (hw : 0<w) (hd : 0<d) (hc : 0<c)
    (rankFit : nWires (guarded F)≤2^w) (clauseFit : (guarded F).length≤2^h)
    (rows : List (RowBook w r h)) (cols : ColBook w)
    (order : List (Old (guarded F))) (exhaustive : ∀ v,v∈order)
    (exactRow : rows=order.map (rowSpec (guarded F) C)) (exactCol : cols=colSpec (guarded F)) :
    let run := compileFromBooks (c:=c) (d:=d) (nWires (guarded F))
      ((Finset.univ : Finset V).toList.map code) (codeCNF code F) rows cols
    ∃ output : CNFPortFile F r c d,run.result=some output.raw ∧ output.codec=C := by
  have a := recovered_actual_unsigned_atlas (guarded F) C hw rankFit hd hc rows cols order
    exhaustive exactRow exactCol
  dsimp only [compileFromBooks]
  rw [a]
  exact paid_compact_root_ingress F code inj C clauseFit _ rfl

theorem paid_original_compact_from_books_fee (F : CNF V)
    (code : V→List Bool) (inj : Function.Injective code) {w r c d h vw : ℕ}
    (C : LiteralCodec (physicalPlant (guarded F)) r c d)
    (hw : 0<w) (hd : 0<d) (hc : 0<c)
    (rankFit : nWires (guarded F)≤2^w) (degree : ∀ a∈F,a.length≤3)
    (wordWidth : ∀ v,(code v).length=vw)
    (rows : List (RowBook w r h)) (cols : ColBook w)
    (order : List (Old (guarded F))) (exhaustive : ∀ v,v∈order)
    (exactRow : rows=order.map (rowSpec (guarded F) C)) (exactCol : cols=colSpec (guarded F)) :
    let n := nWires (guarded F)
    let run := compileFromBooks (c:=c) (d:=d) n
      ((Finset.univ : Finset V).toList.map code) (codeCNF code F) rows cols
    run.steps≤recoveredFee c d n rows cols+
      (fullIngressFee vw 3 F.length (Fintype.card V)+
        (1+n*signFee r c d h 4 (F.length+Fintype.card V))+5)+6 := by
  have L : ∀ s∈rows,s.ranks.length≤2^d := by
    rw [exactRow]
    intro s hs
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hs
    change (List.ofFn (fun j : Fin (J7R10Ports.degree (guarded F) v) =>
      rowRank (w:=w) (guarded F) ⟨v,j⟩)).length≤2^d
    rw [List.length_ofFn]
    exact C.portFit v
  have K : cols.length≤2^c := by rw [exactCol,colSpec,List.length_ofFn]; exact C.columnFit
  have a := recovered_actual_unsigned_atlas (guarded F) C hw rankFit hd hc rows cols order
    exhaustive exactRow exactCol
  have b := recovered_atlas_fee (nWires (guarded F)) rows cols hw hd hc rankFit L K
  have f := paid_full_ingress_fee F code inj vw wordWidth degree
    (List.ofFn (positionForWire (guarded F) C : Fin (nWires (guarded F))→Position r c d h))
  rw [List.length_ofFn] at f
  dsimp only [compileFromBooks]
  rw [a]
  dsimp only
  omega

#print axioms emitted_rows_billed
#print axioms flatten_pair_chunk_length
#print axioms emitted_columns_billed
#print axioms recovered_atlas_fee
#print axioms paid_original_compact_from_books
#print axioms paid_original_compact_from_books_fee
end J6R50RootIngress
