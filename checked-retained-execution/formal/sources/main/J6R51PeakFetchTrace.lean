
import J6R26DescriptorTreeRegistry

/-! An observational trace of the actually executed sequential
header search. Erasing observations returns the original Meter.
On a failed comparison fetch still copies that row's bytes.
The trace records a sequence of individual observations, never
an assertion that the executor retains the entire trace. -/
namespace J6R51Peak
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree

set_option autoImplicit false
set_option maxHeartbeats 3100000

structure ReadEvent (w : ℕ) where
  row : DirRow w
  copied : List Bool
  hit : Bool
  cost : ℕ

def headerReadEvent {w : ℕ} (addr : Word w) (row : DirRow w) : ReadEvent w :=
  let matchId := cmpAddr addr row.id
  let result := copyBytes row.bytes
  ⟨row,result.result,matchId.result,matchId.steps+result.steps+2*w+6⟩

def observedFetch {w : ℕ} (addr : Word w) :
    List (DirRow w) → Meter (Option (List Bool)) × List (ReadEvent w)
  | [] => (⟨none,2⟩,[])
  | row::tail =>
    let e := headerReadEvent addr row
    if e.hit then (⟨some e.copied,e.cost⟩,[e])
    else
      let rest := observedFetch addr tail
      (⟨rest.1.result,e.cost+rest.1.steps⟩,e::rest.2)

theorem observed_fetch_erases {w : ℕ} (addr : Word w) (bank : List (DirRow w)) :
    (observedFetch addr bank).1=fetch addr bank := by
  induction bank with
  | nil => rfl
  | cons row rest ih =>
    simp only [observedFetch,headerReadEvent,fetch]
    split <;> simp only [ih]

theorem live_read_is_real_copy {w : ℕ} (addr : Word w) (row : DirRow w) :
    let e := headerReadEvent addr row
    e.copied=row.bytes ∧ (e.hit=true↔addr=row.id) ∧ e.cost=rowFee row := by
  have cmp := cmpAddr_exact addr row.id
  dsimp only [headerReadEvent]
  refine ⟨?_,cmp.1,?_⟩
  · rw [copyBytes_exact]
  · rw [copyBytes_exact,cmp.2]
    unfold rowFee
    change 10*w+5+(3*row.bytes.length+1)+2*w+6=_
    omega

theorem recorded_read_was_of_actual_row {w : ℕ} (addr : Word w) (bank : List (DirRow w))
    (e : ReadEvent w) (recorded : e∈(observedFetch addr bank).2) :
    e.row∈bank ∧ e=headerReadEvent addr e.row := by
  induction bank with
  | nil => simp [observedFetch] at recorded
  | cons row rest ih =>
    rw [observedFetch] at recorded
    dsimp only at recorded
    split at recorded
    · have h := List.mem_singleton.mp recorded
      subst e
      exact ⟨List.mem_cons_self,rfl⟩
    · rcases List.mem_cons.mp recorded with he | he
      · subst e
        exact ⟨List.mem_cons_self,rfl⟩
      · obtain ⟨mem,eq⟩ := ih he
        exact ⟨List.mem_cons_of_mem _ mem,eq⟩

theorem fresh_search_reads_all_rows {w : ℕ} (addr : Word w) (bank : List (DirRow w))
    (fresh : ∀ row∈bank,row.id≠addr) :
    observedFetch addr bank=⟨⟨none,fetchFee bank⟩,bank.map (headerReadEvent addr)⟩ := by
  induction bank with
  | nil => rfl
  | cons row rest ih =>
    let e := headerReadEvent addr row
    have hh : e.hit≠true := fun h=>fresh row List.mem_cons_self
      (((live_read_is_real_copy addr row).2.1.mp h).symm)
    rw [observedFetch,if_neg hh]
    dsimp only
    rw [ih (fun x hx=>fresh x (List.mem_cons_of_mem _ hx)),List.map_cons,fetchFee]
    rw [(live_read_is_real_copy addr row).2.2]

theorem recheck_reads_only_new_head {w : ℕ} (row : DirRow w) (bank : List (DirRow w)) :
    observedFetch row.id (row::bank)=
      (⟨some row.bytes,rowFee row⟩,[headerReadEvent row.id row]) := by
  have h := live_read_is_real_copy row.id row
  rw [observedFetch,if_pos (h.2.1.mpr rfl)]
  rw [h.1,h.2.2]

def readWorkingFields {w : ℕ} (e : ReadEvent w) : List Bool :=
  e.copied++[e.hit]

theorem observed_row_working_width {w : ℕ} (addr : Word w)
    (bank : List (DirRow w)) (e : ReadEvent w) (shown : e∈(observedFetch addr bank).2) :
    (readWorkingFields e).length=e.row.bytes.length+1 ∧ e.row∈bank := by
  obtain ⟨mem,eq⟩ := recorded_read_was_of_actual_row addr bank e shown
  have h : e.copied=e.row.bytes := eq ▸ (live_read_is_real_copy addr e.row).1
  exact ⟨by simp only [readWorkingFields,List.length_append,h]; rfl,mem⟩

#print axioms observed_fetch_erases
#print axioms live_read_is_real_copy
#print axioms recorded_read_was_of_actual_row
#print axioms fresh_search_reads_all_rows
#print axioms recheck_reads_only_new_head
#print axioms observed_row_working_width
end J6R51Peak
