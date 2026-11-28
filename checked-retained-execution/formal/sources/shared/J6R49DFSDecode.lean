import J6R48DFSModeProbe

/-! Decode just the emitted exponent word, in the given physical
variable order. In particular there is no lookup through the list of
all legal exponent tuples and no finite choice of a matching tuple.
The Nat operations and the proof/type-level conversion are not by
themselves a measured binary decoder. -/
namespace J6R49DFS
open scoped Polynomial
open J6R15ModeCost J6R16ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint

set_option autoImplicit false
set_option maxRecDepth 2300
set_option maxHeartbeats 5500000

noncomputable def assemble {A : Type*} [DecidableEq A] : List A→List ℕ→A→₀ℕ
  | x::xs,b::bs => Finsupp.single x b+assemble xs bs
  | _,_ => 0

theorem assemble_off {A : Type*} [DecidableEq A] (xs : List A) (bs : List ℕ) (x : A)
    (h : x∉xs) : assemble xs bs x=0 := by
  induction xs generalizing bs with
  | nil => cases bs <;> rfl
  | cons y ys ih =>
    obtain ⟨hn,ht⟩ : x≠y ∧ x∉ys := by simpa only [List.mem_cons,not_or] using h
    cases bs with
    | nil => rfl
    | cons b bs => simp [assemble,hn,ih bs ht]

theorem assembled_vector {A : Type*} [DecidableEq A] (xs : List A) (nd : xs.Nodup) (bs : List ℕ)
    (len : bs.length=xs.length) :
    xs.map (assemble xs bs)=bs := by
  induction xs generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons => simp at len
  | cons x xs ih =>
    cases bs with
    | nil => simp at len
    | cons b bs =>
      obtain ⟨hx,hxs⟩ := List.nodup_cons.mp nd
      have hL : bs.length=xs.length := Nat.succ.inj len
      have hOne : assemble (x::xs) (b::bs) x=b := by
        simp [assemble,assemble_off xs bs x hx]
      have hTail : xs.map (assemble (x::xs) (b::bs))=xs.map (assemble xs bs) := by
        apply List.map_congr_left
        intro y hy
        have hNe : y≠x := by
          intro e
          subst y
          exact hx hy
        simp [assemble,hNe]
      rw [List.map_cons,hOne,hTail,ih hxs bs hL]

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}

noncomputable def assembledAt (I : SiteTape sel d t q) (bs : List ℕ) :
    (shape S Δ sel).Mode c t→₀ℕ :=
  letI := (shape S Δ sel).decideMode c t
  assemble (I.modes.map (site_mode_equiv sel d t).symm) bs

theorem assembled_at_key (I : SiteTape sel d t q) (bs : List ℕ) (len : bs.length=I.modes.length) :
    I.modes.map (fun m=>assembledAt I bs ((site_mode_equiv sel d t).symm m))=bs := by
  letI := (shape S Δ sel).decideMode c t
  let z := (site_mode_equiv sel d t).symm
  have h := assembled_vector (I.modes.map z) (I.nodup.map z.injective) bs
    (len.trans (List.length_map z).symm)
  simpa only [List.map_map,Function.comp_apply,assembledAt,z] using h

theorem raw_assembled_legal (I : SiteTape sel d t q) (bs : List ℕ) (len : bs.length=I.modes.length)
    (budget : weightedDegree (I.modes.map modeWeight) bs<registerPrecision S c t) :
    assembledAt I bs ∈ @J6RecursiveMenu.menu ((shape S Δ sel).Mode c t)
      ((shape S Δ sel).finiteMode c t) ((shape S Δ sel).decideMode c t)
      (registerPrecision S c t) ((shape S Δ sel).weight c t) := by
  letI := (shape S Δ sel).finiteMode c t
  letI := (shape S Δ sel).decideMode c t
  have hpos (m : (shape S Δ sel).Mode c t) : 0<(shape S Δ sel).weight c t m := by
    rw [site_mode_weight sel d t]
    exact (modeWeight_bounds _).1
  apply (J6RecursiveMenu.exact_printed_menu (registerPrecision S c t)
    ((shape S Δ sel).weight c t) hpos (assembledAt I bs)).mpr
  rw [←roster_is_menu_weight (site_mode_equiv sel d t) ((shape S Δ sel).weight c t)
    modeWeight (site_mode_weight sel d t) I.modes I.nodup I.allModes,
    assembled_at_key I bs len]
  exact budget

/-- Reject malformed length or too-high weight, without traversing the
exponential menu. No legal value is supplied by the caller. -/
noncomputable def decodeAt (I : SiteTape sel d t q) (ws : List (Word q)) :
    Option (NativeMenu (shape S Δ sel) c t) :=
  let bs := ws.map Word.val
  if gate : bs.length=I.modes.length ∧
      weightedDegree (I.modes.map modeWeight) bs<registerPrecision S c t then
    some ⟨assembledAt I bs,raw_assembled_legal I bs gate.1 gate.2⟩
  else none

theorem decode_one_legal_vector (I : SiteTape sel d t q) (ws : List (Word q))
    (ok : (ws.map Word.val).length=I.modes.length ∧
      weightedDegree (I.modes.map modeWeight) (ws.map Word.val)<registerPrecision S c t) :
    ∃ β,decodeAt I ws=some β ∧ vectorKey sel d t I β=ws.map Word.val := by
  let β : NativeMenu (shape S Δ sel) c t :=
    ⟨assembledAt I (ws.map Word.val),raw_assembled_legal I _ ok.1 ok.2⟩
  exact ⟨β,by simp only [decodeAt,dif_pos ok,β],assembled_at_key I _ ok.1⟩

theorem decode_canonical_mode_words (I : SiteTape sel d t q)
    (β : NativeMenu (shape S Δ sel) c t)
    (fit : ∀ k∈vectorKey sel d t I β,k<2^q) :
    decodeAt I ((vectorKey sel d t I β).map word)=some β := by
  letI := (shape S Δ sel).finiteMode c t
  letI := (shape S Δ sel).decideMode c t
  have E : ((vectorKey sel d t I β).map (word (q:=q))).map Word.val=vectorKey sel d t I β := by
    rw [List.map_map]
    exact List.map_congr_left (fun k hk=>word_val (fit k hk)) |>.trans (List.map_id _)
  have hL : (vectorKey sel d t I β).length=I.modes.length := List.length_map _
  have hD : weightedDegree (I.modes.map modeWeight) (vectorKey sel d t I β)<registerPrecision S c t := by
    unfold vectorKey
    rw [roster_is_menu_weight (site_mode_equiv sel d t) ((shape S Δ sel).weight c t)
      modeWeight (site_mode_weight sel d t) I.modes I.nodup I.allModes]
    exact (J6RecursiveMenu.exact_printed_menu _ _
      (fun x=>by rw [site_mode_weight sel d t]; exact (modeWeight_bounds _).1) β.val).mp β.property
  obtain ⟨γ,hγ,eγ⟩ := decode_one_legal_vector I ((vectorKey sel d t I β).map word) (by rw [E]; exact ⟨hL,hD⟩)
  have h : γ=β := vector_key_inj sel d t I (eγ.trans E)
  exact h ▸ hγ

theorem decode_invalid_vector (I : SiteTape sel d t q) (ws : List (Word q))
    (h : I.modes.length≠ws.length ∨
      registerPrecision S c t≤weightedDegree (I.modes.map modeWeight) (ws.map Word.val)) :
    decodeAt I ws=none := by
  unfold decodeAt
  refine dif_neg ?_
  intro v
  rw [List.length_map] at v
  exact h.elim (fun e=>e v.1.symm) (fun e=>not_lt_of_ge e v.2)

#print axioms assemble_off
#print axioms assembled_vector
#print axioms assembled_at_key
#print axioms raw_assembled_legal
#print axioms decode_one_legal_vector
#print axioms decode_canonical_mode_words
#print axioms decode_invalid_vector
end J6R49DFS
