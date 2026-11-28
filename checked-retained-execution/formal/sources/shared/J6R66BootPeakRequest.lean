import J6R57PublicRequestImage

/-! Serialized selected fields of the genuine public request image, and
a compositional cut for its actual block emitter. A serialized row counts
all three views even if some word references are physically shared. This
does not count proof objects, allocator metadata, or arbitrary suppliers. -/
namespace J6R66.BootPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000
set_option maxRecDepth 3700
set_option Elab.async false

def bitSize {A : Type*} (encode : A→List Bool) (rows : List A) : ℕ :=
  (rows.flatMap encode).length

theorem bitSize_append {A : Type*} (encode : A→List Bool) (left right : List A) :
    bitSize encode (left++right)=bitSize encode left+bitSize encode right := by
  simp only [bitSize,List.flatMap_append,List.length_append]

theorem bitSize_exact {A : Type*} (encode : A→List Bool) (rows : List A) (width : ℕ)
    (size : ∀ x,(encode x).length=width) :
    bitSize encode rows=rows.length*width := by
  induction rows with
  | nil => simp only [bitSize,List.flatMap_nil,List.length_nil,Nat.zero_mul]
  | cons x xs ih =>
    change (encode x++xs.flatMap encode).length=(xs.length+1)*width
    rw [List.length_append,size,show (xs.flatMap encode).length=xs.length*width from ih,
      Nat.add_mul,Nat.one_mul,Nat.add_comm width]

theorem bitSize_take {A : Type*} (encode : A→List Bool) (rows : List A) (atMost : ℕ) :
    bitSize encode (rows.take atMost)≤bitSize encode rows := by
  have bound := Nat.le_add_right (bitSize encode (rows.take atMost))
    (bitSize encode (rows.drop atMost))
  rwa [←bitSize_append,List.take_append_drop] at bound

def entryBits {kp m n tc tj tw : ℕ} {mark : Word kp} (e : Entry mark m n tc tj tw) : List Bool :=
  e.head.data.centre.bits++e.head.data.sample.bits++e.head.data.magnitude.bits++
  e.wire.centre.bits++e.wire.sample.bits++e.wire.group.bits++e.id.bits

def entryWidth (kp tc tj tw : ℕ) : ℕ := tc+tj+tw+tc+tj+6+KeyWidth kp tc tj

theorem entry_bits_exact {kp m n tc tj tw : ℕ} {mark : Word kp}
    (e : Entry mark m n tc tj tw) : (entryBits e).length=entryWidth kp tc tj tw := by
  simp only [entryBits,entryWidth,List.length_append,e.head.data.centre.size,
    e.head.data.sample.size,e.head.data.magnitude.size,e.wire.centre.size,
    e.wire.sample.size,e.wire.group.size,e.id.size]

def publicCount (m n : ℕ) : ℕ := (m+1)*(literalDegree m n+1)*64

section Cuts
variable {I A : Type*} (f : I→Meter (List A))

/-- The same pending prepend/fee continuation as the actual emitter. -/
def resumeBooks (head : List I) (suffix : Meter (List A)) : Meter (List A) :=
  head.foldr (fun i rest=>
    let made := f i
    let out := prependRows rest.result made.result
    ⟨out.result,made.steps+rest.steps+out.steps+3⟩) suffix

theorem actual_book_emitter_continues_from_suffix (front rear : List I) :
    emitBooks f (front++rear)=resumeBooks f front (emitBooks f rear) := by
  induction front with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,emitBooks,resumeBooks,List.foldr_cons] at *
    rw [ih]

theorem actual_book_pending_and_suffix_are_the_returned_fields
    (encode : A→List Bool) (front rear : List I) (k : ℕ) :
    let prior := (emitBooks f front).result
    let later := (emitBooks f rear).result
    let full := (emitBooks f (front++rear)).result
    bitSize encode prior+bitSize encode later=bitSize encode full ∧
    bitSize encode prior+bitSize encode later+bitSize encode (full.take k)≤2*bitSize encode full := by
  let prior := (emitBooks f front).result
  let later := (emitBooks f rear).result
  let full := (emitBooks f (front++rear)).result
  have h : full=prior++later := by
    change (emitBooks f (front++rear)).result=(emitBooks f front).result++(emitBooks f rear).result
    rw [(emitted_books_exact f (front++rear)).1,(emitted_books_exact f front).1,
      (emitted_books_exact f rear).1,List.flatMap_append]
  have bits : bitSize encode prior+bitSize encode later=bitSize encode full := by
    rw [h,bitSize_append]
  have cap := bitSize_take encode full k
  refine ⟨bits,?_⟩
  change bitSize encode prior+bitSize encode later+bitSize encode (full.take k)≤2*bitSize encode full
  omega
end Cuts

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew)
variable (I : SharedInputs G ell q rr cc dd prec kp bw)

theorem actual_request_image_has_exact_catalogue_bits :
    bitSize entryBits (buildRequestImage W I).result.tables.requests.rows=
      publicCount m native*entryWidth kp tc tj tw := by
  rw [bitSize_exact _ _ _ entry_bits_exact,actual_request_image_row_count]
  rfl

theorem actual_catalogue_book_cut_bits (front rear : List (HeadIndex m native))
    (cut : orderedHeads m native=front++rear) (k : ℕ) :
    let image := (buildRequestImage W I).result
    let emit := emitGroupBook W image.compiled.mark
    emitCatalogue W image.compiled.mark=resumeBooks emit front (emitBooks emit rear) ∧
    bitSize entryBits (emitBooks emit front).result+
      bitSize entryBits (emitBooks emit rear).result+
      bitSize entryBits (image.tables.requests.rows.take k)≤
      2*(publicCount m native*entryWidth kp tc tj tw) := by
  let image := (buildRequestImage W I).result
  let emit := emitGroupBook W image.compiled.mark
  have h : emitCatalogue W image.compiled.mark=emitBooks emit (front++rear) := by
    unfold emitCatalogue
    rw [cut]
  refine ⟨h.trans (actual_book_emitter_continues_from_suffix emit front rear),?_⟩
  have fit := (actual_book_pending_and_suffix_are_the_returned_fields emit entryBits front rear k).2
  rw [←h,←image.tables.requests.ordered] at fit
  have e := actual_request_image_has_exact_catalogue_bits W I
  change bitSize entryBits image.tables.requests.rows=_ at e
  rw [e] at fit
  exact fit

#print axioms bitSize_exact
#print axioms bitSize_take
#print axioms actual_book_emitter_continues_from_suffix
#print axioms actual_book_pending_and_suffix_are_the_returned_fields
#print axioms actual_request_image_has_exact_catalogue_bits
#print axioms actual_catalogue_book_cut_bits
end
end J6R66.BootPeak
