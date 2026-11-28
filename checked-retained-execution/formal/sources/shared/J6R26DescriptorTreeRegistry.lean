import J6R25PreparedSupplyChildStage

/-! Purely binary immutable directory. Exact fresh cost, including
scanning past all previous rows, copying the inserted bytes, and
refetching the actual first row. A collision produces an explicit miss
certificate; it does not pass an old descriptor to the wrong call. -/
namespace J6R26DescriptorTree
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply

theorem lookup_miss_exact {w : ℕ} (id : Word w) (bank : List (DirRow w))
    (fresh : ∀ row∈bank,row.id≠id) : fetch id bank=⟨none,fetchFee bank⟩ := by
  induction bank with
  | nil => rfl
  | cons x xs ih =>
    have hcmp : (cmpAddr id x.id).result≠true :=
      fun h=>fresh x List.mem_cons_self ((cmpAddr_exact id x.id).1.mp h).symm
    have hTail := ih (fun row h=>fresh row (List.mem_cons_of_mem _ h))
    rw [fetch,if_neg hcmp,hTail,copyBytes_exact,(cmpAddr_exact id x.id).2]
    have h : 10*w+5+(3*x.bytes.length+1)+2*w+6+fetchFee xs=fetchFee (x::xs) := by
      simp only [fetchFee,rowFee]
      omega
    exact congrArg (fun t=>(⟨none,t⟩ : Meter (Option (List Bool)))) h

theorem lookup_head_exact {w : ℕ} (x : DirRow w) (bank : List (DirRow w)) :
    fetch x.id (x::bank)=⟨some x.bytes,rowFee x⟩ := by
  have hcmp : (cmpAddr x.id x.id).result=true := (cmpAddr_exact _ _).1.mpr rfl
  rw [fetch,if_pos hcmp,copyBytes_exact,(cmpAddr_exact x.id x.id).2]
  have h : 10*w+5+(3*x.bytes.length+1)+2*w+6=rowFee x := by
    unfold rowFee
    omega
  exact congrArg (fun t=>(⟨some x.bytes,t⟩ : Meter (Option (List Bool)))) h

def checkedInstall {w : ℕ} (entry : Meter (DirRow w)) (bank : List (DirRow w)) :
    Meter (List (DirRow w)×Option (List Bool)) :=
  let probe := fetch entry.result.id bank
  match probe.result with
  | some _ => ⟨(bank,none),entry.steps+probe.steps+5⟩
  | none =>
    let copy := copyBytes entry.result.bytes
    let write : DirRow w := ⟨entry.result.id,copy.result⟩
    let next := write::bank
    let read := fetch entry.result.id next
    ⟨(next,read.result),entry.steps+probe.steps+copy.steps+2*w+8+read.steps+4⟩

def installFee {w : ℕ} (entry : Meter (DirRow w)) (bank : List (DirRow w)) :=
  entry.steps+fetchFee bank+3*entry.result.bytes.length+2*w+9+rowFee entry.result+4

theorem fresh_install_exact {w : ℕ} (entry : Meter (DirRow w)) (bank : List (DirRow w))
    (fresh : ∀ row∈bank,row.id≠entry.result.id) :
    checkedInstall entry bank=⟨(entry.result::bank,some entry.result.bytes),installFee entry bank⟩ := by
  unfold checkedInstall
  dsimp only
  rw [lookup_miss_exact entry.result.id bank fresh,copyBytes_exact]
  dsimp only
  have e : (⟨entry.result.id,entry.result.bytes⟩ : DirRow w)=entry.result := by
    cases entry.result
    rfl
  rw [e,lookup_head_exact]
  have h : entry.steps+fetchFee bank+(3*entry.result.bytes.length+1)+2*w+8+rowFee entry.result+4=
      installFee entry bank := by
    unfold installFee
    omega
  exact congrArg (fun t=>(⟨(entry.result::bank,some entry.result.bytes),t⟩ :
    Meter (List (DirRow w)×Option (List Bool)))) h

theorem fresh_install_old_visible {w : ℕ} (entry : Meter (DirRow w)) (bank : List (DirRow w))
    (fresh : ∀ row∈bank,row.id≠entry.result.id) (id : Word w) (disj : entry.result.id≠id) :
    (fetch id (checkedInstall entry bank).result.1).result=(fetch id bank).result := by
  rw [fresh_install_exact entry bank fresh]
  exact preserved_read entry.result id bank disj

#print axioms lookup_miss_exact
#print axioms lookup_head_exact
#print axioms fresh_install_exact
#print axioms fresh_install_old_visible
end J6R26DescriptorTree

