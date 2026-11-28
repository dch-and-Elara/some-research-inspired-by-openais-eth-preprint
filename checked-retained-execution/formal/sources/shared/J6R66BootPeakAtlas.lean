import J6R66BootPeakShared
import J6R66BootPeakInit
import J6R48DFSPayload
import J6R51PeakDirectory

/-! Observe the actual complete Page requests, native chart output, and
widened publication buffer in the R35 prepared root seed. The original
per-page compiler is used, and the Page size guard is about its returned
rows. Internal compiler/list allocator scratch is not identified with
these serialized snapshots. -/
namespace J6R66.BootPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R17ModeTape J6R32RootGeneratedRegistryInputs J6R54PeakInput J6R55SelectedPeak J6R24MeteredRecursion
open J6R48DFS J6R33PageIndexedBirth J6R33StatefulArithmeticPage J6R21Ancestor
open J6R30ProducedGateRegistry J6R51Peak J6R12CollisionEdges J6R14LayoutCost J6R32ChildResidentTransfer
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22000000
set_option maxRecDepth 4800
set_option Elab.async false

def pageRequestBits {q w : ℕ} (req : Request q w) : List Bool :=
  pageRefBits req.owner++req.key.bits

theorem physical_request_width {a b : ℕ} (p : P11FullPacking.Page a b (Fin 64)) (q w : ℕ) :
    (pageRequestBits (sourceRequest q w p)).length=6*a+6*a+q+(w+13*a) := by
  unfold pageRequestBits pageRefBits sourceRequest pageRef
  simp only [List.length_append,wordCell,coordinateLabel_len,
    (word (q:=q) (orderedPage a b p).2.val).size,(childPageKey w p).size]

private theorem bitSize_exact_on {A : Type*} (encode : A→List Bool) (rows : List A)
    (width : ℕ) (fit : ∀ x∈rows,(encode x).length=width) :
    bitSize encode rows=rows.length*width := by
  induction rows with
  | nil => simp only [bitSize,List.flatMap_nil,List.length_nil,Nat.zero_mul]
  | cons x xs ih =>
    change (encode x++xs.flatMap encode).length=(xs.length+1)*width
    rw [List.length_append,fit x List.mem_cons_self,
      show (xs.flatMap encode).length=xs.length*width from ih (fun y hy=>fit y (List.mem_cons_of_mem x hy)),
      Nat.add_mul,Nat.one_mul,Nat.add_comm width]

def atlasRowBits {a p ell q w : ℕ} {old : List (A1R10.Word p)} {i : Fin a}
    (row : PageRow a p ell q w old i) : List Bool :=
  row.address.bits++originPayload row.payload

theorem widened_rows_keep_the_same_page_payload
    {a p ell q w : ℕ} {old : List (A1R10.Word p)} {i : Fin a}
    (full : List (PageRow a p ell q w old i)) (U ext : ℕ)
    (size : ∀ y∈full,(originPayload y.payload).length≤U) :
    bitSize atlasRowBits full≤full.length*(w+U) ∧
    bitSize atlasRowBits (full.map (mappedRow ext))≤full.length*(w+ext+U) := by
  refine ⟨bitSize_le atlasRowBits full (w+U) ?_,?_⟩
  · intro x hx
    simp only [atlasRowBits,List.length_append,x.address.size]
    exact Nat.add_le_add_left (size x hx) w
  · have h := bitSize_le atlasRowBits (full.map (mappedRow ext)) (w+ext+U) (by
      intro x hx
      obtain ⟨src,hs,rfl⟩ := List.mem_map.mp hx
      rw [atlasRowBits,List.length_append,(mappedRow ext src).address.size]
      exact Nat.add_le_add_left (size src hs) (w+ext))
    rwa [List.length_map] at h

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec key bw tc tj tw edgew : ℕ}
variable (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)

def exteriorPageRequests :=
  writeRequests (a m) (RootKey m) X.hq X.copies

theorem actual_exterior_requests_have_exact_bytes :
    let req := exteriorPageRequests X
    req.result.length=pagesCount (a m) (K m) ∧
    bitSize pageRequestBits req.result=pagesCount (a m) (K m)*(6*a m+6*a m+q+pageKeyWidth m) := by
  let out := exteriorPageRequests X
  obtain ⟨geometry,len,_⟩ := write_requests_exact (a m) (RootKey m) X.hq
    X.copies X.copiesOK X.copyFits
  refine ⟨len,?_⟩
  have exactRow : ∀ r∈out.result,(pageRequestBits r).length=6*a m+6*a m+q+pageKeyWidth m := by
    intro r h
    change r∈(writeRequests (a m) (RootKey m) X.hq X.copies).result at h
    rw [geometry] at h
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp h
    exact physical_request_width k q (RootKey m)
  exact (bitSize_exact_on pageRequestBits out.result _ exactRow).trans
    (congrArg (·*(6*a m+6*a m+q+pageKeyWidth m)) len)

theorem literal_exterior_table_size :
    (rootTable X.chosenFields).length=pagesCount (a m) (K m) := by
  unfold rootTable
  rw [List.length_map,(child_pages_complete (a m) (K m)).2.2]
  rfl

theorem actual_cached_compiler_output_is_the_counted_native_table
    (S : ActualRootPreparation G ell q) (same : S=(rootPreparationFor X).result) :
    let req := exteriorPageRequests X
    let common := commonFromResident S.frame X.hf S.probes m S.resident X.group X.sample X.code
    let atlas := buildPages common.result S.frame.hp X.positive X.qFits.le req.result
    (alignPages (congrArg (fun x : ActualRootPreparation G ell q=>x.frame.words) same) atlas).result=
      some (rootTable X.chosenFields) := by
  subst S
  change (atlasUsingShared X (rootPreparationFor X).result).result=_
  exact (shared_atlas_is_literal X).1.symm.trans (Classical.choose_spec (stable_exterior_atlas X)).1

theorem actual_exterior_atlas_mount_cut_bits
    (S : ActualRootPreparation G ell q) (same : S=(rootPreparationFor X).result) (pad U : ℕ)
    (each : ∀ y∈rootTable X.chosenFields,(originPayload y.payload).length≤U)
    (ri ni wi : ℕ) :
    let req := exteriorPageRequests X
    let native := rootTable X.chosenFields
    let job := preparedSeed X S same pad
    let packed := job.expected.pages
    job.built.result=some job.expected ∧ packed.length=pagesCount (a m) (K m) ∧
    bitSize pageRequestBits (req.result.take ri)+bitSize atlasRowBits (native.take ni)+
      bitSize atlasRowBits (packed.take wi)≤
      pagesCount (a m) (K m)*
        ((6*a m+6*a m+q+pageKeyWidth m)+(pageKeyWidth m+U)+(pageKeyWidth m+pad+U)) := by
  let job := preparedSeed X S same pad
  let native := rootTable X.chosenFields
  let count := pagesCount (a m) (K m)
  have nativeLen : native.length=count := literal_exterior_table_size X
  have shape : job.expected.pages=native.map (mappedRow pad) := rfl
  have len : job.expected.pages.length=count := by rw [shape,List.length_map,nativeLen]
  refine ⟨job.validBody,len,?_⟩
  have req := (bitSize_take pageRequestBits (exteriorPageRequests X).result ri).trans_eq
    (actual_exterior_requests_have_exact_bytes X).2
  obtain ⟨old,padded⟩ := widened_rows_keep_the_same_page_payload native U pad each
  rw [nativeLen] at old padded
  have p := (bitSize_take atlasRowBits job.expected.pages wi)
  rw [shape] at p
  have o := (bitSize_take atlasRowBits native ni).trans old
  calc
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add req o) (p.trans padded)
    _ = _ := by simp only [count,Nat.mul_add]

#print axioms physical_request_width
#print axioms widened_rows_keep_the_same_page_payload
#print axioms actual_exterior_requests_have_exact_bytes
#print axioms actual_cached_compiler_output_is_the_counted_native_table
#print axioms actual_exterior_atlas_mount_cut_bits
end
end J6R66.BootPeak
