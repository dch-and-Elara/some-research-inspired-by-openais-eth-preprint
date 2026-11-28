import J6R34ChildPathOrdinal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8500000

/-! True child half-port rows occur in the descriptor issued by the
actual R26 occurrence. This is a structured receipt, not a parser
for unfenced variable-length concatenation. -/
namespace J6R34ChildPath
open scoped Polynomial Classical
open AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R10Repack J6R11Blueprint J6R12Blueprint J6ActiveRun
open J1PPrinted J6R24MeteredRecursion J6R26DescriptorTree

private theorem flat_fragment {A : Type*} (enc : A→List Bool) (xs : List A) (x : A) (h : x∈xs) :
    ∃ left right, xs.flatMap enc=left++enc x++right := by
  induction xs with
  | nil => exact (List.not_mem_nil h).elim
  | cons y rest ih =>
    rcases List.mem_cons.mp h with e|e
    · subst y
      exact ⟨[],rest.flatMap enc,rfl⟩
    · obtain ⟨a,b,E⟩ := ih e
      refine ⟨enc y++a,b,?_⟩
      simp only [List.flatMap_cons,E,List.append_assoc]

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)

theorem issued_log_contains_actual_half_port {port edgeW dep prec tc tz tm key : ℕ}
    (J : NativeJob T v port edgeW dep prec tc tz tm)
    (issuance : Meter (Word key)) (u : v.child.host.Edge) :
    let record := J.physical.record (childHalves T v u).val
    (J.job.make issuance).result.id=issuance.result ∧
      ∃ left right, (J.job.make issuance).result.bytes=left++rowBytes record++right := by
  let h := childHalves T v u
  let portRec := J.physical.record h.val
  have hg : physicalGroup sel (ticketReady T v) v.centerAt h.val=v.groupAt := h.property
  have mem : h.val∈J.physical.physicalSelected v.groupAt :=
    List.mem_filter.mpr ⟨J.physical.complete h.val,decide_eq_true hg⟩
  obtain ⟨p,q,hSplit⟩ := flat_fragment rowBytes ((J.physical.physicalSelected v.groupAt).map
    J.physical.record) portRec (List.mem_map_of_mem mem)
  obtain ⟨id,bytes⟩ := J.literal_bytes issuance
  refine ⟨id,?_⟩
  refine ⟨J.coordinates++ (word (q:=prec) v.child.prec).bits++ (word (q:=dep) v.child.depth).bits++
    (word (q:=edgeW) v.child.edges).bits++p,q,?_⟩
  rw [bytes,hSplit]
  simp only [childHeaderBytes,List.append_assoc]
  rfl

private def tinyRecord (k : ℕ) (body : List Bool) : PortRow 2 := ⟨word k,word 0,body⟩

/-- Fixed row count and distinct addresses do not frame arbitrary
body lengths in `rowBytes`. Even the two legal, all-zero group
lists here disagree on the second edge's address. -/
theorem unfenced_row_log_ambiguous :
    ∃ l r : List (PortRow 2),
      l.length=2 ∧ r.length=2 ∧
      (l.map PortRow.address).Nodup ∧ (r.map PortRow.address).Nodup ∧
      (∀ u∈l,u.group=word 0) ∧ (∀ u∈r,u.group=word 0) ∧
      (serializeRows l).result=(serializeRows r).result ∧
      l.map PortRow.address≠r.map PortRow.address := by
  let l := [tinyRecord 0 [], tinyRecord 1 (rowBytes (tinyRecord 2 []))]
  let r := [tinyRecord 0 (rowBytes (tinyRecord 1 [])),tinyRecord 2 []]
  have distinct (a b : ℕ) (ha : a<4) (hb : b<4) (hn : a≠b) :
      word (q:=2) a≠word b := by
    intro h
    have s := congrArg Word.val h
    rw [word_val ha,word_val hb] at s
    exact hn s
  refine ⟨l,r,rfl,rfl,?_,?_,?_,?_,rfl,?_⟩
  · change ([word (q:=2) 0,word 1] : List (Word 2)).Nodup
    exact List.nodup_cons.mpr
      ⟨fun hy=>distinct 0 1 (by decide) (by decide) (by decide) (List.mem_singleton.mp hy),List.nodup_singleton _⟩
  · change ([word (q:=2) 0,word 2] : List (Word 2)).Nodup
    exact List.nodup_cons.mpr
      ⟨fun hy=>distinct 0 2 (by decide) (by decide) (by decide) (List.mem_singleton.mp hy),List.nodup_singleton _⟩
  · intro x mem
    simp only [l,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with h|h <;> subst x <;> rfl
  · intro x mem
    simp only [r,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with h|h <;> subst x <;> rfl
  · intro eq
    change ([word (q:=2) 0,word 1] : List (Word 2))=[word 0,word 2] at eq
    exact distinct 1 2 (by decide) (by decide) (by decide) (List.cons.inj (List.cons.inj eq).2).1

#print axioms issued_log_contains_actual_half_port
#print axioms unfenced_row_log_ambiguous
end J6R34ChildPath
