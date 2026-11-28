import J6R33PageIndexedBirthCodec

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5200000

/-! The real charged cell header stream, including empty cells, and
real binary copy range produce a complete list of physical page keys.
No list of already computed keys or packets is supplied to the generator. -/
namespace J6R33PageIndexedBirth
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeLocal
open J6R15ModeCost J6R17ModeTape J6R27OriginalGate J6R14LayoutCost J6R31RootResidentTables
open J6R32ChildResidentTransfer P11FullPacking J6R12CollisionEdges J6R24LegalLayout J6R30GeneratedRootLayout

def requestSlice {q : ℕ} (a w : ℕ) (words : List (Word q)) (h : ExportBox) :
    Meter (List (Request q (w+13*a))) :=
  mapMeter (emitRequest a w h) words

def writeRequests {q : ℕ} (a w : ℕ) (hq : 0<q) (copies : Word q) :
    Meter (List (Request q (w+13*a))) :=
  let H := makeHeaders a
  let C := wordSpan hq copies
  let written := flatMeter (requestFee a w q) (requestSlice a w C.result) H.result
  ⟨written.result,H.steps+C.steps+written.steps+4⟩

def pagesCount (a b : ℕ) : ℕ := (2^(6*a)*2^(6*a))*b

def requestsFee (a w q b : ℕ) : ℕ :=
  headerBankFee a+spanFee q b+
    (2^(6*a)*2^(6*a))*((2*requestFee a w q+6)*b+8)+4

theorem write_requests_exact {q b : ℕ} (a w : ℕ) (hq : 0<q)
    (copies : Word q) (count : copies.val=b) (addrFit : b≤2^w) :
    let X := writeRequests a w hq copies
    X.result=(orderedChildPages a b).map (sourceRequest q w) ∧
      X.result.length=pagesCount a b ∧ X.steps≤requestsFee a w q b := by
  let H := makeHeaders a
  let C := wordSpan hq copies
  let W := flatMeter (requestFee a w q) (requestSlice a w C.result) H.result
  have fitQ : b≤2^q := (count ▸ val_lt copies).le
  obtain ⟨Hval,Hfee⟩ := header_bank_exact a
  obtain ⟨Cval,Cfee⟩ := wordSpan_exact hq copies
  change H.result=_ at Hval
  change H.steps≤_ at Hfee
  change C.result=_ at Cval
  change C.steps=_ at Cfee
  rw [count,range_words] at Cval
  have Hlen : H.result.length=2^(6*a)*2^(6*a) := (actual_header_fields a).2.2
  have Clen : C.result.length=b := by rw [Cval,List.length_map,List.length_finRange]
  have slice (h : ExportBox) (hh : h∈H.result) :
      let f := fun h => C.result.map (fun j=>(emitRequest a w h j).result)
      (requestSlice a w C.result h).result=f h ∧
        (requestSlice a w C.result h).steps≤(requestFee a w q+6)*b ∧ (f h).length=b := by
    rw [Hval,List.mem_map] at hh
    obtain ⟨c,_,rfl⟩ := hh
    have ok (x : Word q) (hx : x∈C.result) :
        (emitRequest a w (headerBox c) x).steps≤requestFee a w q := by
      rw [Cval,List.mem_map] at hx
      obtain ⟨j,_,rfl⟩ := hx
      exact (emitted_request_exact c j q w fitQ addrFit).2
    obtain ⟨val,cost⟩ := mapMeter_exact (emitRequest a w (headerBox c))
      (fun j=>(emitRequest a w (headerBox c) j).result) (requestFee a w q)
      C.result (fun x hx=>⟨rfl,ok x hx⟩)
    change (requestSlice a w C.result (headerBox c)).result=_ at val
    change (requestSlice a w C.result (headerBox c)).steps≤_ at cost
    rw [Clen] at cost
    exact ⟨val,cost,by simp only [List.length_map,Clen]⟩
  obtain ⟨Wv,Wl,Wc⟩ := flatMeter_exact (requestFee a w q)
    ((requestFee a w q+6)*b) b (requestSlice a w C.result)
    (fun h=>C.result.map (fun j=>(emitRequest a w h j).result)) H.result slice
  change W.result=_ at Wv
  change W.result.length=_ at Wl
  change W.steps≤_ at Wc
  rw [Hlen] at Wl Wc
  refine ⟨?_,Wl,?_⟩
  · change W.result=_
    rw [Wv,Hval,Cval]
    unfold orderedChildPages
    simp only [List.flatMap_map,List.map_map,List.product,List.map_flatMap]
    apply congrArg (fun f : CellType a→List (Request q (w+13*a))=>(typedCells a).flatMap f)
    funext c
    apply List.map_congr_left
    intro j _
    exact (emitted_request_exact c j q w fitQ addrFit).1
  · change H.steps+C.steps+W.steps+4≤_
    rw [count] at Cfee
    unfold requestsFee
    have ida : (requestFee a w q+6)*b+requestFee a w q*b+8=
        (2*requestFee a w q+6)*b+8 := by ring
    rw [ida] at Wc
    omega

open J6R21Ancestor J6R30ProducedGateRegistry

variable {p ell a q code w : ℕ} {old : List (A1R10.Word p)} {i : Fin a}

def compileAtlas (C : Common old a q code (w+13*a))
    (hp : 0<p) (hv : 0<ell) (fit : i.val+1≤q) (hq : 0<q) (copies : Word q) :
    Meter (Option (List (PageRow a p ell q (w+13*a) old i))) :=
  let made := writeRequests a w hq copies
  let stored := buildPages C hp hv fit made.result
  ⟨stored.result,made.steps+stored.steps+4⟩

/-- Exact map, key uniqueness, complete lookup, and actually metered
per-page compilation. The proof argument refers only to success of
the actual compiler (and its verified uniform price). -/
theorem compile_atlas_exact {b maxFee : ℕ}
    (C : Common old a q code (w+13*a))
    (hp : 0<p) (hv : 0<ell) (fit : i.val+1≤q) (hq : 0<q) (copies : Word q)
    (count : copies.val=b) (addrFit : b≤2^w)
    (F : Page a b (Fin 64)→PageFields a p ell q old i)
    (localHit : ∀ k,((C.atRequest (sourceRequest q w k)).compile hp hv fit).result=some (F k))
    (localFee : ∀ k : Page a b (Fin 64),((C.atRequest (sourceRequest q w k)).compile hp hv fit).steps≤maxFee) :
    let out := compileAtlas C hp hv fit hq copies
    let bank : List (PageRow a p ell q (w+13*a) old i) :=
      (orderedChildPages a b).map (fun k=>⟨childPageKey w k,F k⟩)
    out.result=some bank ∧ (bank.map RefRow.address).Nodup ∧
      (∀ k,(locate (childPageKey w k) bank).result=some (F k)) ∧
      out.steps≤requestsFee a w q b+pagesCount a b*(maxFee+onePageFee (w+13*a)+5)+6 := by
  let D := orderedChildPages a b
  let Q := writeRequests a w hq copies
  let run := buildPages C hp hv fit Q.result
  obtain ⟨oldVal,_,oldFee⟩ := write_requests_exact a w hq copies count addrFit
  change Q.result=D.map (sourceRequest q w) at oldVal
  change Q.steps≤_ at oldFee
  obtain ⟨newVal,newFee⟩ := build_pages_exact C hp hv fit D (sourceRequest q w) F
    (fun j _=>localHit j)
  rw [←oldVal] at newVal newFee
  have hRun : run.steps≤2+pagesCount a b*(maxFee+onePageFee (w+13*a)+5) := by
    change run.steps=_ at newFee
    rw [newFee]
    apply Nat.add_le_add_left
    have hs : (D.map (fun k=>((C.atRequest (sourceRequest q w k)).compile hp hv fit).steps+
        onePageFee (w+13*a)+5)).sum≤
        D.length*(maxFee+onePageFee (w+13*a)+5) := by
      induction D with
      | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,le_rfl]
      | cons x xs ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
        have e := localFee x
        omega
    have l : D.length=pagesCount a b := (child_pages_complete a b).2.2
    simpa only [l] using hs
  obtain ⟨nd,complete,_⟩ := child_pages_complete a b
  let key := childPageKey (a:=a) (b:=b) w
  have injective : Function.Injective key := child_page_key_injective w addrFit
  refine ⟨newVal,atlas_keys_distinct D nd key injective F,
    (fun k=>atlas_lookup_present D key injective F k (complete k)),?_⟩
  change Q.steps+run.steps+4≤_
  omega

#print axioms write_requests_exact
#print axioms compile_atlas_exact
end J6R33PageIndexedBirth