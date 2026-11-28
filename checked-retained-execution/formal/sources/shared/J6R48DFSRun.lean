import J6R48DFSScope
import J6R33StatefulArithmeticPageWhole

/-! The checked active interpreter is reused without changing an
interpolation center, binary sample, mode order, group order, or leaf
machine. Each real child installs its own page bank exactly where the
append-only interpreter would install it; the sibling sees only the
restored caller state. There is no pre-materialized job tree. -/
namespace J6R48DFS
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R16ModeCost

set_option autoImplicit false
set_option maxRecDepth 2500

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

set_option maxHeartbeats 4200000 in
noncomputable def nativeScoped (R : PagedResident T key prec tw bw page) (retire : J→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) :
    SM L (Block (T.frame p.reached) ell) :=
  if stop : c.edges≤(S).cutoff then
    fun B=>let out := (R.leaf p stop).execute hf (T.frame p.reached) T.vPositive B
           ⟨(out.result,B),out.steps⟩
  else
    let active := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel p.reached T.rootStable active
    activeS (T.active c p.reached active) (reachable_positive T p.reached) T.vPositive hf
      (fun t z m g=>
        let w := addressed (sel:=sel) d t z m g
        withScope retire (R.births p w).job (nativeScoped R retire ((Plan sel).child c w) (.step p w))
          (zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp))
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

theorem native_scoped_leaf (R : PagedResident T key prec tw bw page) (retire : J→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (stop : c.edges≤(S).cutoff) (B : L) :
    nativeScoped R retire c p B=
      let out := (R.leaf p stop).execute hf (T.frame p.reached) T.vPositive B
      (⟨(out.result,B),out.steps⟩ : Meter (Block (T.frame p.reached) ell×L)) := by
  rw [nativeScoped,dif_pos stop]

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
set_option maxHeartbeats 11400000 in
theorem native_scoped_sound (R : PagedResident T key prec tw bw page) (retire : J→ℕ)
    (initial : L) (root : R.rootLive initial) (legal : ReadyOnStack R.births initial)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) :
    Sound (fun B=>B=stackBank R.births initial p)
      (nativeScoped R retire c p) (reference T c p.reached) := by
  by_cases stop : c.edges≤(S).cutoff
  · intro B e
    subst B
    let b := stackBank R.births initial p
    have live : opened R.births R.rootLive p b :=
      stack_is_opened R.births initial R.rootLive R.stableRoot root legal p
    have same := (live_paged_leaf_source R p stop b live).trans (T.correctAt c p.reached).symm
    rw [native_scoped_leaf R retire p stop,reference_leaf (T:=T) p.reached stop]
    refine ⟨((R.leaf p stop).execute hf (T.frame p.reached) T.vPositive b).steps,?_⟩
    exact ⟨frame_words_injective hf (T.frame p.reached) same,by simp only [bare,Nat.zero_add,b],rfl⟩
  · let a := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let A := T.active c p.reached a
    let ph := reachable_positive T p.reached
    let here := stackBank R.births initial p
    let run : ActiveChildS (sel:=sel) L T.bank d := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      withScope retire (R.births p w).job (nativeScoped R retire ((Plan sel).child c w) (.step p w))
        (zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp)
    let ans : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      reference T ((Plan sel).child c w) (reach_snoc (Plan sel) p.reached w)
    rw [nativeScoped,dif_neg stop,reference,dif_neg stop]
    change Sound (fun B=>B=here) (activeS A ph T.vPositive hf run) (A.eval ph T.vPositive hf ans)
    apply active_sound A ph T.vPositive hf run ans
    intro t z β g B eq
    subst B
    let w := addressed (sel:=sel) d t z β g
    let j := (R.births p w).job
    let hχ := nativeScoped R retire ((Plan sel).child c w) (.step p w)
    let b : Meter (Block (T.bank (registerPrecision S c t) (register_positive d t)) ell) :=
      zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp
    have q := native_scoped_sound R retire initial root legal ((Plan sel).child c w) (.step p w)
    obtain ⟨extra,h⟩ := q (afterOne here j) rfl
    change ∃ δ,AgreesAt (fun B=>B=here) (withScope retire j hχ b here) (ans t z β g) δ
    rw [paid_scope_exact retire j hχ b here (legal p w)]
    refine ⟨publishFee here j.entry j.offset j.built+extra+retire j+4,⟨h.value,?_,rfl⟩⟩
    change publishFee here j.entry j.offset j.built+(hχ (afterOne here j)).steps+retire j+4=
      (ans t z β g).steps+(publishFee here j.entry j.offset j.built+extra+retire j+4)
    have fee : (hχ (afterOne here j)).steps=(ans t z β g).steps+extra := h.fee
    rw [fee]
    omega
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

theorem whole_scoped_source (R : PagedResident T key prec tw bw page) (retire : J→ℕ)
    (initial : L) (root : R.rootLive initial) (legal : ReadyOnStack R.births initial)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) :
    let B := stackBank R.births initial p
    let out := nativeScoped R retire c p B
    (T.frame p.reached).decode out.result.1=(sourceBlueprint sel r hf).program.run c ∧
      out.result.2=B := by
  obtain ⟨_,h⟩ := native_scoped_sound R retire initial root legal c p _ rfl
  exact ⟨(congrArg (T.frame p.reached).decode h.value).trans (reference_source T c p.reached),h.invariant⟩

/-- This compares semantic results only; the two directory fee ledgers
differ. The scoped run requires only freshness against active readers. -/
theorem scope_preserves_legal_append_value (R : PagedResident T key prec tw bw page) (retire : J→ℕ)
    (initial : L) (root : R.rootLive initial) (legal : ReadyOnStack R.births initial)
    (ready : JobsReady initial (pagedLog R r .root).jobs) :
    (nativeScoped R retire r .root initial).result.1=
      (nativePaged R r .root initial).result.1 := by
  have a := (whole_scoped_source R retire initial root legal r .root).1
  have b := (whole_paged_root R initial ready root).1
  exact frame_words_injective hf (T.frame (NativeReach.reflexive r)) (a.trans b.symm)

#print axioms nativeScoped
#print axioms native_scoped_leaf
#print axioms native_scoped_sound
#print axioms whole_scoped_source
#print axioms scope_preserves_legal_append_value
end J6R48DFS
