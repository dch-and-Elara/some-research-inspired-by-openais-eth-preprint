import J6R63OrdinalEmitLaw
import J6R49DFSProbe
import J6R58OrdinalSpaceAlignment

/-! At a true site, all archive dependence is in propositions:
completeness/order, a sufficient counter width, and the suffix proof.
Only the physical tuple words, real starting cursor and finite ordinal
are consumed by the running probe. -/
namespace J6R63Ordinal
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS
open J6R58OrdinalSpace

set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3800
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 6400000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s q b : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {t : Center (printedParams (f:=f) (ell:=ell) s) c}
local notation "Menu" => (NativeMenu (N sel) c t)
def HonestArchive (I : J6R16ModeCost.SiteTape sel d t q)
    (ordinal : NativeMenu (N sel) c t → ℕ) (b : ℕ) : Prop :=
  ∃ seq : List (NativeMenu (N sel) c t), seq.length < 2^b ∧ PrefixNames ordinal seq ∧
    seq.map (vectorKey sel d t I)=tupleSpec I

abbrev SuffixFits (I : J6R16ModeCost.SiteTape sel d t q)
    (ordinal : NativeMenu (N sel) c t → ℕ) (p : Pending q I.words.length) (i : Word b) : Prop :=
  AlignedFit (vectorKey sel d t I) ordinal p i

def LegalRaw (I : J6R16ModeCost.SiteTape sel d t q)
    (ordinal : NativeMenu (N sel) c t → ℕ) (raw : List (Word q)) (i : Word b) : Prop :=
  ∃ β : NativeMenu (N sel) c t, decodeAt I raw=some β ∧
    (raw.map Word.val=vectorKey sel d t I β ∧ i.val=ordinal β)

variable (I : J6R16ModeCost.SiteTape sel d t q) (ordinal : NativeMenu (N sel) c t → ℕ)
local notation "Encode" => (vectorKey sel d t I)

theorem actual_ordinal_at_decoding {raw : List (Word q)} {i : Word b} {β : Menu}
    (h : LegalRaw I ordinal raw i) (decoded : decodeAt I raw=some β) :
    raw.map Word.val=Encode β ∧ i.val=ordinal β := by
  obtain ⟨γ,hit,rank⟩ := h
  have e := Option.some.inj (hit.symm.trans decoded)
  exact e ▸ rank

theorem native_paid_emit_law (hb : 0<b) :
    EmissionLaw (SuffixFits (b:=b) I ordinal) (LegalRaw I ordinal) := by
  constructor
  intro p i raw st emitted live
  have law := actual_cursor_supplies_its_prefix_address (q:=q) (n:=I.words.length) Encode ordinal hb
  obtain ⟨⟨β,trueRow,rank⟩,more⟩ := law.next p i raw st emitted live
  have hit : decodeAt I raw=some β := by
    have canonical : (raw.map Word.val).map (word (q:=q))=raw := by
      rw [List.map_map]
      exact (List.map_congr_left (fun x (_ : x∈raw)=>valued_word x)).trans (List.map_id _)
    have bytes : raw=(Encode β).map (word (q:=q)) :=
      canonical.symm.trans (congrArg (List.map (word (q:=q))) trueRow)
    rw [bytes]
    exact decode_canonical_mode_words I β (actual_legal_coordinates_fit I β)
  exact ⟨⟨β,hit,trueRow,rank⟩,more⟩

theorem real_cursor_starts_with_checked_archival_rank (hq : 0<q) (archive : HonestArchive I ordinal b)
    (p : Pending q I.words.length) (started : (startingCursor I hq).result=some p) :
    SuffixFits I ordinal p (firstOrdinal b).result := by
  obtain ⟨seq,room,names,matching⟩ := archive
  obtain ⟨beg,found,_,trace⟩ := starting_cursor_exact I hq
  have e : beg=p := Option.some.inj (found.symm.trans started)
  subst beg
  refine ⟨seq,room,names,real_first_pending_starts_at_zero_rank Encode seq p ?_⟩
  simpa only [matching] using trace

#print axioms actual_ordinal_at_decoding
#print axioms native_paid_emit_law
#print axioms real_cursor_starts_with_checked_archival_rank
end
end J6R63Ordinal
