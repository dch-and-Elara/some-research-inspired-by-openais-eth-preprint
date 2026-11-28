
import J6R51PeakFetchTrace
import J6R51PeakDirectory

/-! The exact existing R26 checked-header installation: scan old rows,
copy the descriptor after the fresh guard, then reread the physical
new head once. The selected transient buffers are attached to those
operations, not inferred from an arbitrary Meter label. -/
namespace J6R51Peak
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree

set_option autoImplicit false
set_option maxHeartbeats 3800000

structure HeaderInstallObservation (key : ℕ) where
  run : Meter (List (DirRow key)×Option (List Bool))
  before : List (ReadEvent key)
  written : Option (List Bool)
  after : List (ReadEvent key)

def observeCheckedInstall {key : ℕ} (entry : Meter (DirRow key))
    (bank : List (DirRow key)) : HeaderInstallObservation key :=
  let probe := observedFetch entry.result.id bank
  match probe.1.result with
  | some _ => ⟨⟨(bank,none),entry.steps+probe.1.steps+5⟩,probe.2,none,[]⟩
  | none =>
    let copy := copyBytes entry.result.bytes
    let write : DirRow key := ⟨entry.result.id,copy.result⟩
    let next := write::bank
    let read := observedFetch entry.result.id next
    ⟨⟨(next,read.1.result),entry.steps+probe.1.steps+copy.steps+2*key+8+read.1.steps+4⟩,
      probe.2,some copy.result,read.2⟩

theorem observed_install_erases {key : ℕ} (entry : Meter (DirRow key))
    (bank : List (DirRow key)) :
    (observeCheckedInstall entry bank).run=checkedInstall entry bank := by
  simp only [observeCheckedInstall,checkedInstall,observed_fetch_erases]
  cases (fetch entry.result.id bank).result <;> rfl

theorem actual_fresh_install_has_exact_trace {key : ℕ} (entry : Meter (DirRow key))
    (bank : List (DirRow key)) (fresh : ∀ row∈bank,row.id≠entry.result.id) :
    let o := observeCheckedInstall entry bank
    o.run=⟨(entry.result::bank,some entry.result.bytes),installFee entry bank⟩ ∧
      o.before=bank.map (headerReadEvent entry.result.id) ∧
      o.written=some entry.result.bytes ∧
      o.after=[headerReadEvent entry.result.id entry.result] := by
  dsimp only
  refine ⟨(observed_install_erases entry bank).trans (fresh_install_exact entry bank fresh),?_⟩
  unfold observeCheckedInstall
  rw [fresh_search_reads_all_rows entry.result.id bank fresh]
  dsimp only
  rw [copyBytes_exact]
  dsimp only
  have same : (⟨entry.result.id,entry.result.bytes⟩ : DirRow key)=entry.result := by cases entry.result; rfl
  rw [same,recheck_reads_only_new_head]
  exact ⟨rfl,rfl,rfl⟩

def selectedInstallSnapshots {key : ℕ} (entry : Meter (DirRow key))
    (bank : List (DirRow key)) : List (List Bool) :=
  let o := observeCheckedInstall entry bank
  o.before.map (fun ev=>headerFields entry.result++readWorkingFields ev) ++
    o.written.toList.map (fun buf=>headerFields entry.result++buf) ++
    o.after.map (fun ev=>headerFields entry.result++headerFields ev.row++readWorkingFields ev)

theorem native_read_temporary_length {key : ℕ} (addr : Word key) (row : DirRow key) :
    (readWorkingFields (headerReadEvent addr row)).length=row.bytes.length+1 := by
  simp only [readWorkingFields,List.length_append,(live_read_is_real_copy addr row).1,
    List.length_cons,List.length_nil]

/-- Selected work encodings relative to the incoming bank. They
include the newly prepared entry, one actual copy/comparison, and
the provisional installed header when already present. In particular
this does not keep an array of all old probe buffers. -/
theorem actual_fresh_install_temporary_bits {key U : ℕ} (entry : Meter (DirRow key))
    (bank : List (DirRow key)) (fresh : ∀ row∈bank,row.id≠entry.result.id)
    (fit : ∀ row∈bank,row.bytes.length≤U) (fitEntry : entry.result.bytes.length≤U)
    (bits : List Bool) (isSelected : bits∈selectedInstallSnapshots entry bank) :
    bits.length≤2*key+3*U+1 := by
  obtain ⟨_, h,c,r⟩ := actual_fresh_install_has_exact_trace entry bank fresh
  unfold selectedInstallSnapshots at isSelected
  dsimp only at isSelected
  rw [h,c,r] at isSelected
  simp only [List.mem_append,Option.toList_some,List.map_cons,List.map_nil,List.mem_singleton] at isSelected
  rcases isSelected with (hist | written) | again
  · simp only [List.map_map,Function.comp_def] at hist
    obtain ⟨row,member,eq⟩ := List.mem_map.mp hist
    have bound := fit row member
    rw [←eq,List.length_append,exact_header_encoding,native_read_temporary_length]
    omega
  · rw [written,List.length_append,exact_header_encoding]
    omega
  · rw [again]
    have h : (headerReadEvent entry.result.id entry.result).row=entry.result := rfl
    simp only [List.length_append,h,exact_header_encoding,native_read_temporary_length]
    omega

#print axioms observed_install_erases
#print axioms actual_fresh_install_has_exact_trace
#print axioms native_read_temporary_length
#print axioms actual_fresh_install_temporary_bits
end J6R51Peak
