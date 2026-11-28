import J6R35GatewayPreparationSeed
import J6R34OfficialGatewayAtlas

/-! Only the proved identity of the installed immutable seed is used
to transport an already valid inherited route. This keeps exactly the
same paid descendant inputs and actual leaf functions. -/
namespace J6R36SharedGateway
open scoped Polynomial Classical
open Polynomial AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R11Blueprint J6R12Blueprint J1PPrinted J6R10Reachable
open J6R24MeteredRecursion J6R34RootAtlas J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R21Ancestor J6R26DescriptorTree
set_option maxHeartbeats 10000000
set_option maxRecDepth 2300
set_option linter.unusedSectionVars false

section Rebase
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable {actual : InputFamily T key prec tw bw page}
variable {old new : PageJob f ell key prec tw bw page}

def rebaseRoutes (invariant : IsLive old=IsLive new)
    (R : RoutedInputs actual old) : RoutedInputs actual new where
  leaf := R.leaf
  route := by
    intro c p stop B live x v
    apply R.route p stop B ?_ x v
    rw [invariant]
    exact live

abbrev PhysicalLeaves :=
  ∀ {c : Call (PhysicalHost f ell)}, Path sel r c →
    c.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff → PagedLeaf c key page

theorem resident_data_ext
    (L R : PagedResident T key prec tw bw page)
    (b : (@L.births : Births T key prec tw bw page)=@R.births)
    (e : L.rootLive=R.rootLive)
    (w : (@L.leaf : PhysicalLeaves (key:=key) (page:=page) (sel:=sel) (r:=r))=@R.leaf) : L=R := by
  rcases L with ⟨lb,lI,lS,lw,lR⟩
  rcases R with ⟨rb,rI,rS,rw0,rR⟩
  change @lb = @rb at b
  change lI=rI at e
  change @lw = @rw0 at w
  subst rb
  subst rI
  subst rw0
  rfl

theorem same_anchored_resident (invariant : IsLive old=IsLive new)
    (R : RoutedInputs actual old) :
    compilerResident actual new (rebaseRoutes invariant R)=compilerResident actual old R := by
  exact resident_data_ext _ _ rfl invariant.symm rfl

end Rebase

section Publication
variable {key prec tw bw : ℕ} {D A : Type*}
local notation "L" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D

theorem jobs_ready_same_head_id (B : L) (old new : J) (js : List J)
    (id : new.identifier=old.identifier) (ready : JobsReady B (old::js)) :
    JobsReady B (new::js) := by
  refine ⟨ready.1,?_,?_⟩
  · change (new.identifier::(js.map Job.identifier)).Nodup
    rw [id]
    exact ready.2.1
  · intro k hk row hrow
    rcases List.mem_cons.mp hk with same|rest
    · subst k
      rw [id]
      exact ready.2.2 old List.mem_cons_self row hrow
    · exact ready.2.2 k (List.mem_cons_of_mem _ rest) row hrow

theorem with_published_on_success (B : L) (j : J) (go : SM L A) (bad : Meter A)
    (ok : (j.install B).result.2=true) :
    withPublished j go bad B=
      ⟨(go (j.install B).result.1).result,(j.install B).steps+(go (j.install B).result.1).steps+4⟩ := by
  unfold withPublished
  dsimp only
  rw [if_pos ok]

theorem same_published_continuation (B : L) (old new : J) (go : SM L A) (bad : Meter A)
    (ok : (old.install B).result.2=true) (state : (new.install B).result=(old.install B).result) :
    let n := withPublished new go bad B
    let o := withPublished old go bad B
    n.result=o.result ∧
      n.steps=(new.install B).steps+(go (old.install B).result.1).steps+4 ∧
      o.steps=(old.install B).steps+(go (old.install B).result.1).steps+4 := by
  have okN : (new.install B).result.2=true := (congrArg Prod.snd state).trans ok
  rw [with_published_on_success B new go bad okN,with_published_on_success B old go bad ok]
  dsimp only
  rw [state]
  exact ⟨rfl,rfl,rfl⟩

end Publication

#print axioms rebaseRoutes
#print axioms resident_data_ext
#print axioms same_anchored_resident
#print axioms jobs_ready_same_head_id
#print axioms with_published_on_success
#print axioms same_published_continuation
end J6R36SharedGateway
