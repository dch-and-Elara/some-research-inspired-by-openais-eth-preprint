import J6R30ProducedGateRegistryFrames

set_option autoImplicit false
set_option warningAsError true

/-! One invocation owns many distinct packet pages. An actual
R27 compilation per requested physical page makes the page rows;
a compact chart and a pure proof of successful local decoding do
not pre-provide any row payload. The common frame and stamp stay
outside this bank and are shared by its parent occurrence. -/
namespace J6R33PageIndexedBirth
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost
  J6R17ModeTape J6R27OriginalGate J6R30ProducedGateRegistry J6R21Ancestor J6R20Ancestor

structure Request (q key : ℕ) where
  owner : PageRef q
  key : Word key

structure Common {p : ℕ} (fw : List (A1R10.Word p)) (a q code key : ℕ) where
  axis : List Bool
  group : Word 6
  start : Word code
  raw : List (RawMode q)
  sparse : List (RawMode q×Word q)
  masks : List (MaskRow q)
  seats : List (SeatField a key)
  coordinates : {ws : List Bool // ws.length=fw.length}

variable {a p ell q code key : ℕ} {fw : List (A1R10.Word p)} {i : Fin a}

def Common.atRequest (C : Common fw a q code key) (A : Request q key) :
    Frames fw a q code key :=
  ⟨C.axis,A.owner,C.group,C.start,C.raw,C.sparse,C.masks,A.key,C.seats,C.coordinates⟩

abbrev PageFields (a p ell q : ℕ) (fw : List (A1R10.Word p)) (i : Fin a) :=
  OriginFields a p ell q fw i

abbrev PageRow (a p ell q key : ℕ) (fw : List (A1R10.Word p)) (i : Fin a) :=
  RefRow key (PageFields a p ell q fw i)

def onePage (C : Common fw a q code key) (hp : 0<p) (hEll : 0<ell) (fit : i.val+1≤q)
    (A : Request q key) : Meter (Option (PageRow a p ell q key fw i)) :=
  let child := (C.atRequest A).compile hp hEll fit
  match child.result with
  | none=>⟨none,child.steps+3⟩
  | some payload=>
    let stamp := copyFixed A.key
    ⟨some ⟨stamp.result,payload⟩,child.steps+stamp.steps+6⟩

def onePageFee (key : ℕ) : ℕ := 3*key+7

theorem emit_one_exact (C : Common fw a q code key) (hp : 0<p) (hEll : 0<ell) (fit : i.val+1≤q)
    (A : Request q key) (F : PageFields a p ell q fw i)
    (h : ((C.atRequest A).compile hp hEll fit).result=some F) :
    onePage C hp hEll fit A=
      ⟨some ⟨A.key,F⟩,((C.atRequest A).compile hp hEll fit).steps+onePageFee key⟩ := by
  rw [onePage]
  dsimp only
  rw [h,copy_fixed_exact]
  unfold onePageFee
  congr 1

/-- The payload is handed to the outer in-scope record publisher:
none means a genuine page compiler failure, not a default tensor. -/
def buildPages (C : Common fw a q code key) (hp : 0<p) (hEll : 0<ell) (fit : i.val+1≤q) :
    List (Request q key)→Meter (Option (List (PageRow a p ell q key fw i)))
  | []=>⟨some [],2⟩
  | k::ks=>
    let L := onePage C hp hEll fit k
    match L.result with
    | none=>⟨none,L.steps+3⟩
    | some row=>
      let R := buildPages C hp hEll fit ks
      ⟨R.result.map (row::·),L.steps+R.steps+5⟩

variable {I : Type*}

theorem build_pages_exact (C : Common fw a q code key) (hp : 0<p) (hEll : 0<ell)
    (fit : i.val+1≤q) (order : List I) (req : I→Request q key)
    (F : I→PageFields a p ell q fw i)
    (accepted : ∀ j∈order,((C.atRequest (req j)).compile hp hEll fit).result=some (F j)) :
    let out := buildPages C hp hEll fit (order.map req)
    out.result=some (order.map (fun j=>⟨(req j).key,F j⟩)) ∧
      out.steps=2+(order.map (fun j=>((C.atRequest (req j)).compile hp hEll fit).steps+onePageFee key+5)).sum := by
  induction order with
  | nil => simp [buildPages]
  | cons j js ih =>
    have here := emit_one_exact C hp hEll fit (req j) (F j) (accepted j List.mem_cons_self)
    have tail := ih (fun k hk=>accepted k (List.mem_cons_of_mem _ hk))
    obtain ⟨hResult,hSteps⟩ := tail
    simp only [List.map_cons,buildPages,here,hResult,hSteps,Option.map_some,List.sum_cons]
    exact ⟨True.intro,by omega⟩

theorem atlas_keys_distinct {D : Type*} (order : List I) (h : order.Nodup)
    (keyWord : I→Word key) (inj : Function.Injective keyWord) (datum : I→D) :
    ((order.map (fun j=>(⟨keyWord j,datum j⟩ : RefRow key D))).map RefRow.address).Nodup := by
  simpa only [List.map_map,Function.comp_def] using h.map inj

theorem atlas_lookup_present {D : Type*} (order : List I)
    (keyWord : I→Word key) (inj : Function.Injective keyWord) (datum : I→D) (j : I) (hm : j∈order) :
    (locate (keyWord j) (order.map (fun k=>(⟨keyWord k,datum k⟩ : RefRow key D)))).result=some (datum j) := by
  apply locate_hit
  · exact List.mem_map.mpr ⟨j,hm,rfl⟩
  · intro row hr hA
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hr
    have e : k=j := inj hA
    subst k
    rfl

theorem atlas_lookup_absent {D : Type*} (w : Word key) (bank : List (RefRow key D))
    (fresh : ∀ row∈bank,row.address≠w) :
    (locate w bank).result=none := by
  induction bank with
  | nil => rfl
  | cons row tail ih =>
    have h : (cmpAddr w row.address).result=false := Bool.eq_false_iff.mpr
      (fun h=>fresh row List.mem_cons_self ((cmpAddr_exact w row.address).1.mp h).symm)
    rw [locate,h,if_neg Bool.false_ne_true]
    exact ih (fun x hx=>fresh x (List.mem_cons_of_mem _ hx))

#print axioms emit_one_exact
#print axioms build_pages_exact
#print axioms atlas_keys_distinct
#print axioms atlas_lookup_present
#print axioms atlas_lookup_absent
end J6R33PageIndexedBirth