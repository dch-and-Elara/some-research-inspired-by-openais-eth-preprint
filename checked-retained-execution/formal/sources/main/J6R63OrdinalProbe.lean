import J6R63OrdinalSite
import J6R49DFSDirectCentre

/-! Put the true finite ordinal into each of the 64 actual group
reads, inside the maintained halt-driven probe. The child reader is
allowed to charge differently; word equality does not equate fees. -/
namespace J6R63Ordinal
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply
open J6R48DFS J6R49DFS J6R58OrdinalSpace J6R32StatefulArithmetic
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3500
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 20500000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s q b : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {t : Center (printedParams (f:=f) (ell:=ell) s) c}
local notation "pt" => (registerPrecision SP c t)
variable (F : Frame f (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)) (I : SiteTape sel d t q) (ordinal : NativeMenu (N sel) c t → ℕ)
local notation "Encode" => (vectorKey sel d t I)

abbrev RankedChild (AFrame : Frame f (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t))
    (tape : SiteTape sel d t q) (rankOf : NativeMenu (N sel) c t → ℕ) (b : ℕ) : Type :=
  (β : NativeMenu (N sel) c t) → (raw : List (J6R15ModeCost.Word q)) → (i : J6R15ModeCost.Word b) →
    raw.map J6R15ModeCost.Word.val=vectorKey sel d t tape β → i.val=rankOf β → Fin 64 → Meter (Block AFrame ell)

def selectedMode (raw : List (J6R15ModeCost.Word q)) (i : J6R15ModeCost.Word b)
    (allowed : LegalRaw I ordinal raw i) : NativeMenu (N sel) c t :=
  (decodeAt I raw).get (by
    obtain ⟨β,found,_⟩ := allowed
    simp [found])

theorem literal_selected_mode (raw : List (J6R15ModeCost.Word q)) (i : J6R15ModeCost.Word b)
    (allowed : LegalRaw I ordinal raw i) :
    decodeAt I raw=some (selectedMode I ordinal raw i allowed) := by
  unfold selectedMode
  exact (Option.some_get _).symm

def updateRanked (hv : 0<ell) (child : RankedChild F I ordinal b)
    (acc : Block F ell) (raw : List (J6R15ModeCost.Word q)) (i : J6R15ModeCost.Word b)
    (allowed : LegalRaw I ordinal raw i) : Meter (Block F ell) := by
  let β := selectedMode I ordinal raw i allowed
  have returned : decodeAt I raw=some β := literal_selected_mode I ordinal raw i allowed
  have evidence := actual_ordinal_at_decoding I ordinal allowed returned
  exact addM F.hp ⟨acc,0⟩ (product64 F.hp F.sizePos hv (child β raw i evidence.1 evidence.2))

theorem exact_ranked_mode_has_the_same_value (hf : f.Monic) (hv : 0<ell)
    (child : RankedChild F I ordinal b) (ref : NativeMenu (N sel) c t → Fin 64 → Meter (Block F ell))
    (agree : ∀ (β : NativeMenu (N sel) c t) (raw : List (J6R15ModeCost.Word q))
      (i : J6R15ModeCost.Word b) (bits : raw.map J6R15ModeCost.Word.val=vectorKey sel d t I β)
      (rank : i.val=ordinal β) (g : Fin 64), (child β raw i bits rank g).result=(ref β g).result)
    (acc : Block F ell) (raw : List (J6R15ModeCost.Word q)) (i : J6R15ModeCost.Word b)
    (allowed : LegalRaw I ordinal raw i) :
    (updateRanked F I ordinal hv child acc raw i allowed).result=(modeUpdate F I hv ref acc raw).result := by
  have plain : modeUpdate F I hv ref acc raw=
      addM F.hp ⟨acc,0⟩ (product64 F.hp F.sizePos hv (ref (selectedMode I ordinal raw i allowed))) := by
    rw [modeUpdate,literal_selected_mode I ordinal raw i allowed]
  rw [plain]
  unfold updateRanked
  dsimp only
  apply frame_words_injective hf F
  unfold Frame.decode
  congr 1
  rw [addM_read,addM_read,product64_value,product64_value]
  congr 1
  apply Finset.prod_congr rfl
  intro g _
  rw [agree]

def runProbeRanked (hq : 0<q) (hb : 0<b) (hv : 0<ell)
    (archive : HonestArchive I ordinal b) (child : RankedChild F I ordinal b) :
    Meter (Block F ell) :=
  let boot := startingCursor I hq
  let init := zeroM (ell:=ell) (f:=F.words) F.hp
  let i := firstOrdinal b
  match started : boot.result with
  | none => ⟨init.result,init.steps+boot.steps⟩
  | some p =>
    let state := real_cursor_starts_with_checked_archival_rank I ordinal hq archive p started
    let out := checkedDrain _ _ (native_paid_emit_law I ordinal hb)
      (updateRanked F I ordinal hv child) p i.result state init.result (init.steps+boot.steps+i.steps)
    ⟨out.result.1,out.steps⟩

theorem ranked_probe_is_one_paid_cursor_loop (hq : 0<q) (hb : 0<b) (hv : 0<ell)
    (archive : HonestArchive I ordinal b) (child : RankedChild F I ordinal b)
    (p : Pending q I.words.length) (started : (startingCursor I hq).result=some p) :
    let init := zeroM (ell:=ell) (f:=F.words) F.hp
    let i := firstOrdinal b
    let state := real_cursor_starts_with_checked_archival_rank I ordinal hq archive p started
    let out := checkedDrain _ _ (native_paid_emit_law I ordinal hb) (updateRanked F I ordinal hv child)
      p i.result state init.result (init.steps+(startingCursor I hq).steps+i.steps)
    runProbeRanked F I ordinal hq hb hv archive child=⟨out.result.1,out.steps⟩ := by
  unfold runProbeRanked
  dsimp only
  split
  · rename_i no
    rw [started] at no
    cases no
  · rename_i p' got
    have same := Option.some.inj (got.symm.trans started)
    subst p'
    rfl

theorem ranked_probe_keeps_the_actual_online_word (hf : f.Monic) (hq : 0<q) (hb : 0<b)
    (hv : 0<ell) (archive : HonestArchive I ordinal b)
    (child : RankedChild F I ordinal b) (ref : NativeMenu (N sel) c t → Fin 64 → Meter (Block F ell))
    (agree : ∀ (β : NativeMenu (N sel) c t) (raw : List (J6R15ModeCost.Word q)) (i : J6R15ModeCost.Word b) (bits : raw.map J6R15ModeCost.Word.val=Encode β) (rank : i.val=ordinal β) g,
      (child β raw i bits rank g).result=(ref β g).result) :
    (runProbeRanked F I ordinal hq hb hv archive child).result=(runProbe F I hq hv ref).result := by
  obtain ⟨p,started,_,tr⟩ := starting_cursor_exact I hq
  rw [ranked_probe_is_one_paid_cursor_loop F I ordinal hq hb hv archive child p started,runProbe]
  dsimp only
  rw [started]
  exact congrArg Prod.fst (checked_drain_keeps_the_unranked_value _ _
    (native_paid_emit_law I ordinal hb) (updateRanked F I ordinal hv child) (modeUpdate F I hv ref)
    (exact_ranked_mode_has_the_same_value F I ordinal hf hv child ref agree) p (firstOrdinal b).result
    (real_cursor_starts_with_checked_archival_rank I ordinal hq archive p started) _ _ _ _ tr)

#print axioms literal_selected_mode
#print axioms updateRanked
#print axioms exact_ranked_mode_has_the_same_value
#print axioms runProbeRanked
#print axioms ranked_probe_is_one_paid_cursor_loop
#print axioms ranked_probe_keeps_the_actual_online_word
end
end J6R63Ordinal
