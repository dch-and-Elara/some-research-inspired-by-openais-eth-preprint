import J6R50LeafSource

/-! A live owner chart checks the filter *at* the demanded owner; it
does not prohibit extraneous resident lines. The actual implementation
visits all lines even when they cannot affect the command. -/
namespace J6R58LeafScale
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R33StatefulArithmeticPage J6R50Leaf J6R27OriginalGate J6R36ChildFramedRoute
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14000000

def addUnused {own w : ℕ} (unused : ResidentPort own w) (n : ℕ)
    (lines : List (ResidentPort own w)) : List (ResidentPort own w) :=
  List.replicate n unused++lines

theorem adding_unused_preserves_owner_filter {own w : ℕ} (owner : Word own)
    (unused : ResidentPort own w) (miss : owner≠unused.address)
    (lines : List (ResidentPort own w)) (n : ℕ) :
    (addUnused unused n lines).filter (fun x=>(cmpAddr owner x.address).result)=
      lines.filter (fun x=>(cmpAddr owner x.address).result) := by
  have no : (cmpAddr owner unused.address).result=false :=
    Bool.eq_false_iff.mpr (fun h=>miss ((cmpAddr_exact _ _).1.mp h))
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [addUnused,List.replicate_succ,List.cons_append,List.filter_cons,no,Bool.false_eq_true,if_false]
    exact ih

theorem unused_resident_lines_keep_source_command {N own w key prec page b : ℕ}
    (keyAt : Fin N→Word w) (owner : Word own) (unused : ResidentPort own w)
    (miss : owner≠unused.address) (n : ℕ) (lines : List (ResidentPort own w))
    (table : OriginTable own w key prec page) {cmd : PageReadCode N key page}
    (valid : SourceCommand b keyAt lines table owner cmd) :
    SourceCommand b keyAt (addUnused unused n lines) table owner cmd := by
  cases valid with
  | old slot gate fit listed => exact .old slot gate fit listed
  | paged site born pg ports headers slot tag listed actual =>
    refine .paged site born pg ports headers slot tag listed ?_
    rw [adding_unused_preserves_owner_filter owner unused miss lines n]
    exact actual

theorem actual_collect_incoming_pays_unused_lines {own w : ℕ} (owner : Word own)
    (unused : ResidentPort own w) (miss : owner≠unused.address)
    (lines : List (ResidentPort own w)) (n : ℕ) :
    collectIncoming owner (addUnused unused n lines)=
      ⟨(collectIncoming owner lines).result,(collectIncoming owner lines).steps+n*(10*own+11)⟩ := by
  have no : (cmpAddr owner unused.address).result=false :=
    Bool.eq_false_iff.mpr (fun h=>miss ((cmpAddr_exact _ _).1.mp h))
  have fee := (cmpAddr_exact owner unused.address).2
  induction n with
  | zero => simp [addUnused]
  | succ n ih =>
    change collectIncoming owner (unused::addUnused unused n lines)=_
    simp only [collectIncoming,no,Bool.false_eq_true,if_false,ih,fee,Nat.succ_mul]
    congr 1
    omega

theorem real_paged_emitter_pays_unused_lines {N own w key prec page : ℕ}
    (keys : List (Word w)) (owner : Word own) (unused : ResidentPort own w)
    (miss : owner≠unused.address) (lines : List (ResidentPort own w)) (n : ℕ)
    (site : PageOrigin key prec page) (id : Word page) (regular : site.header.pageKey=some id) :
    let original := buildPage N keys owner lines site
    let padded := buildPage N keys owner (addUnused unused n lines) site
    padded.result=original.result ∧ padded.steps=original.steps+n*(10*own+11) := by
  simp only [buildPage,copy_origin_exact,regular,actual_collect_incoming_pays_unused_lines owner unused miss]
  exact ⟨True.intro,by omega⟩

theorem one_selected_page_owner_has_no_uniform_fee {N own w key prec page b : ℕ}
    (keys : List (Word w)) (owner : Word own) (unused : ResidentPort own w)
    (miss : owner≠unused.address) (lines : List (ResidentPort own w))
    (table : OriginTable own w key prec page)
    (site : PageOrigin key prec page) (pID : Word page)
    (hit : (locate owner table).result=some (.paged site))
    (regular : site.header.pageKey=some pID) (bound : ℕ) :
    ∃ n : ℕ,
      let original := buildOwner N b keys lines table owner
      let padded := buildOwner N b keys (addUnused unused n lines) table owner
      padded.result=original.result ∧ bound<padded.steps := by
  refine ⟨bound+1,?_⟩
  have fee := real_paged_emitter_pays_unused_lines (N:=N) keys owner unused miss lines (bound+1)
    site pID regular
  dsimp only at fee
  dsimp only [buildOwner]
  rw [hit]
  dsimp only [buildBody]
  constructor
  · rw [fee.1]
  · rw [fee.2]
    have n : bound+1≤(bound+1)*(10*own+11) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega

#print axioms adding_unused_preserves_owner_filter
#print axioms unused_resident_lines_keep_source_command
#print axioms actual_collect_incoming_pays_unused_lines
#print axioms real_paged_emitter_pays_unused_lines
#print axioms one_selected_page_owner_has_no_uniform_fee
end J6R58LeafScale
