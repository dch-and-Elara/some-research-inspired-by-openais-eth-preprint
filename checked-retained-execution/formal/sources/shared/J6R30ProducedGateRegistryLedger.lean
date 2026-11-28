
import J6R30ProducedGateRegistryHeader
import J6R30ProducedGateRegistryContext

/-! An immutable pair of the genuine R26 byte-header directory and
the genuine R21 reference directory. A successful publication reads
the installed header back, parses its creation-precision word, then
stores the exact result of its supplied finite payload compiler under
the very same occurrence identifier. A failed attempt changes neither
visible table. No already-computed coefficient value is stored. -/
namespace J6R30ProducedGateRegistry
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree

structure Stored (key prec tw bw : ℕ) (D : Type*) where
  stamp : Stamp key prec
  context : CentreContext tw bw
  checkedHeader : List Bool
  payload : D

structure Ledger (key prec tw bw : ℕ) (D : Type*) where
  headers : List (DirRow key)
  records : List (RefRow key (Stored key prec tw bw D))

def Ledger.synced {key prec tw bw : ℕ} {D : Type*} (B : Ledger key prec tw bw D) : Prop :=
  B.headers.map DirRow.id=B.records.map RefRow.address

theorem ref_fresh_from_headers {key prec tw bw : ℕ} {D : Type*}
    (B : Ledger key prec tw bw D) (s : B.synced) (id : Word key)
    (fresh : ∀ row∈B.headers,row.id≠id) : ∀ row∈B.records,row.address≠id := by
  intro r mem h
  have m : r.address∈B.records.map RefRow.address := List.mem_map_of_mem mem
  rw [←s] at m
  obtain ⟨row,atRow,eq⟩ := List.mem_map.mp m
  exact fresh row atRow (eq.trans h)

theorem ref_miss_exact {key : ℕ} {D : Type*} (addr : Word key) (rows : List (RefRow key D))
    (fresh : ∀ row∈rows,row.address≠addr) : locate addr rows=⟨none,locateFee key rows.length⟩ := by
  induction rows with
  | nil => simp [locate,locateFee]
  | cons r rs ih =>
    have neq : (cmpAddr addr r.address).result≠true :=
      fun h=>fresh r List.mem_cons_self ((cmpAddr_exact _ _).1.mp h).symm
    rw [locate,if_neg neq]
    dsimp only
    rw [ih (fun r h=>fresh r (List.mem_cons_of_mem _ h)),(cmpAddr_exact _ _).2]
    simp only [locateFee,List.length_cons,Nat.add_mul,Nat.one_mul]
    congr 1
    omega

def refHeadFee (key : ℕ) := 13*key+13

theorem ref_head_exact {key : ℕ} {D : Type*} (obj : RefRow key D) (rows : List (RefRow key D)) :
    locate obj.address (obj::rows)=⟨some obj.payload,refHeadFee key⟩ := by
  rw [locate,if_pos ((cmpAddr_exact _ _).1.mpr rfl),(cmpAddr_exact _ _).2]
  simp only [refHeadFee]
  congr 1
  omega

theorem ref_old_exact {key : ℕ} {D : Type*} (obj : RefRow key D) (rows : List (RefRow key D))
    (addr : Word key) (different : obj.address≠addr) :
    (locate addr (obj::rows)).result=(locate addr rows).result := by
  rw [locate,if_neg (fun h=>different ((cmpAddr_exact _ _).1.mp h).symm)]

def publishCompiled {key prec tw bw : ℕ} {D : Type*} (B : Ledger key prec tw bw D)
    (entry : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (built : Meter (Option D)) : Meter (Ledger key prec tw bw D×Bool) :=
  let head := checkedInstall entry B.headers
  match head.result.2 with
  | none => ⟨(B,false),head.steps+4⟩
  | some bytes =>
    let created := loadAt prec offset bytes
    let old := locate entry.result.id B.records
    match created.result,old.result,built.result with
    | some c,none,some body =>
      let st := duplicateStamp (⟨entry.result.id,c⟩ : Stamp key prec)
      let h := copyContext ctx
      let row : RefRow key (Stored key prec tw bw D) :=
        ⟨st.result.creator,⟨st.result,h.result,bytes,body⟩⟩
      ⟨(⟨head.result.1,row::B.records⟩,true),
        head.steps+created.steps+old.steps+built.steps+st.steps+h.steps+key+14⟩
    | _,_,_ => ⟨(B,false),head.steps+created.steps+old.steps+built.steps+7⟩

def publishedRow {key prec tw bw : ℕ} {D : Type*} (entry : DirRow key) (created : Word prec)
    (ctx : CentreContext tw bw) (body : D) : RefRow key (Stored key prec tw bw D) :=
  ⟨entry.id,⟨⟨entry.id,created⟩,ctx,entry.bytes,body⟩⟩

def publishFee {key prec tw bw : ℕ} {D : Type*} (B : Ledger key prec tw bw D)
    (entry : Meter (DirRow key)) (offset : ℕ) (built : Meter (Option D)) : ℕ :=
  installFee entry B.headers+headerReadFee prec offset+locateFee key B.records.length+
    built.steps+(3*key+3*prec+12)+contextCopyFee tw bw+key+14

set_option maxHeartbeats 2500000 in
theorem publish_compiled_exact {key prec tw bw : ℕ} {D : Type*} (B : Ledger key prec tw bw D)
    (s : B.synced) (entry : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (built : Meter (Option D)) (out : D) (made : built.result=some out)
    (created : Word prec)
    (parsed : loadAt prec offset entry.result.bytes=⟨some created,headerReadFee prec offset⟩)
    (fresh : ∀ row∈B.headers,row.id≠entry.result.id) :
    publishCompiled B entry offset ctx built =
      ⟨(⟨entry.result::B.headers,publishedRow entry.result created ctx out::B.records⟩,true),
        publishFee B entry offset built⟩ := by
  have h := fresh_install_exact entry B.headers fresh
  have miss := ref_miss_exact entry.result.id B.records (ref_fresh_from_headers B s entry.result.id fresh)
  unfold publishCompiled
  dsimp only
  rw [h]
  dsimp only
  rw [parsed,miss,made]
  simp only [duplicate_stamp_exact,copy_context_exact,publishedRow,publishFee]

theorem same_published_record {key prec tw bw : ℕ} {D : Type*}
    (entry : DirRow key) (created : Word prec) (ctx : CentreContext tw bw) (out : D)
    (B : Ledger key prec tw bw D) (s : B.synced) :
    let row := publishedRow entry created ctx out
    let next : Ledger key prec tw bw D := ⟨entry::B.headers,row::B.records⟩
    next.synced ∧ locate entry.id next.records=⟨some row.payload,refHeadFee key⟩ ∧
      (∀ addr,entry.id≠addr→(locate addr next.records).result=(locate addr B.records).result) := by
  dsimp only
  refine ⟨?_,ref_head_exact _ _,?_⟩
  · unfold Ledger.synced at s ⊢
    simp only [List.map_cons,publishedRow,s]
  · intro addr neq
    exact ref_old_exact _ _ _ neq

#print axioms ref_fresh_from_headers
#print axioms ref_miss_exact
#print axioms ref_head_exact
#print axioms publish_compiled_exact
#print axioms same_published_record
end J6R30ProducedGateRegistry


