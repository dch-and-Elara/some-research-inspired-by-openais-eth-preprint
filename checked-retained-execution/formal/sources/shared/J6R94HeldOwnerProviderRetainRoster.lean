import J6R59PublicRetainedDirectory
import J6R52CacheSourceAdvance

/-! A verified byte-preserving view from the already paid R59 loader's
    roster to the actual cached advance's owner context. No alternate
    raw loader or registry is introduced. -/
namespace J6R94HeldOwnerProvider
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute
open J6R24MeteredRecursion J6R10Repack J6R11Blueprint J6R12Blueprint J6ActiveRun J1PPrinted
open J6R50SourceProducer J6R34RootAtlas J6R53OldOwner J6R58RequestSource
open J6R49SourceLayout J6R52CacheSource J6R51ParentFrames J6R59Public
open J6R52Dispatch J6R53Dispatch J6R57PublicRequest J6R48RawRoute J6R51Online J6R32StatefulArithmetic
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5300
set_option maxHeartbeats 31000000
set_option Elab.async false

abbrev OwnerNames (V : Type) := Σ width : ℕ, V→Word width

def namesAsRawContext {V : Type} {width : ℕ} (a : V→Word width) : OwnerNames V := ⟨width,a⟩

def retypeKeptOwners {V : Type} {gate key prec page : ℕ} {A B : OwnerNames V}
    {a b : V→OwnerData gate key prec page}
    (name : A=B) (values : a=b)
    (held : CompleteRoster A.2 a) : CompleteRoster B.2 b := by
  cases name
  cases values
  exact held

theorem retyped_owners_keep_exact_bytes {V : Type} {gate key prec page : ℕ} {A B : OwnerNames V}
    {a b : V→OwnerData gate key prec page} (name : A=B) (values : a=b) (R : CompleteRoster A.2 a) :
    (retypeKeptOwners name values R).order=R.order ∧ HEq (retypeKeptOwners name values R).raw R.raw := by
  cases name
  cases values
  exact ⟨rfl,HEq.rfl⟩

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page gate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {u : (Plan sel).Slot v.child}
variable (Y : StoredSite T v key prec tw bw page)
variable (gates : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gate)))

def NativeCreationOwnerContext (K : LocalLoad Y u) : Prop :=
  namesAsRawContext (nameCurrentOwner Y)=namesAsRawContext K.advance.next.site.oldKey

theorem actual_next_owner_context_is_the_emitted_directory (K : LocalLoad Y u) :
    namesAsRawContext K.advance.next.site.oldKey=namesAsRawContext K.directory.oldKey := rfl

theorem actual_keepR58_sends_its_own_owner_names
    (cache : CachedParentFrames Y.site) (port : PaidPortIndex Y)
    {q : ℕ} {U : ExplicitSelectedWords Y.site u q}
    (R : Replayed Y.site u q U)
    (source : CompleteRoster Y.site.oldKey (parentData Y gates))
    (H : ParentOwnerHeaders Y.site) (inj : Function.Injective Y.site.oldKey)
    (fallback : Addon (1+(Y.site.ownerWidth+page)) (dim (successorTicket v u)) key prec page)
    (plane : Meter (LoadedPlane Y R))
    (fitDepth : v.child.depth+1<2^Y.input.dep)
    (fitPrec : (successorTicket v u).child.prec<2^prec)
    {raw : List (Word (q+1))} (dispatchData : Meter (RawFields R raw)) :
    let op := keepR58OwnerLoad Y gates cache port R source H inj fallback plane fitDepth fitPrec dispatchData
    NativeCreationOwnerContext Y op.result.load := by
  dsimp only [NativeCreationOwnerContext]
  rw [actual_next_owner_context_is_the_emitted_directory]
  rfl

variable (K : HeldOwnerLoad Y (u:=u) gates) (cache : CachedParentFrames Y.site)

theorem creation_context_matches_the_real_cached_child (h : NativeCreationOwnerContext Y K.load) :
    namesAsRawContext (nameCurrentOwner Y)=namesAsRawContext (cachedAdvance Y u K.load cache).next.site.oldKey := by
  rw [cached_advance_exact]
  exact h

def carriedRosterForCachedChild (h : NativeCreationOwnerContext Y K.load) :
    CompleteRoster (cachedAdvance Y u K.load cache).next.site.oldKey
      (parentData (cachedAdvance Y u K.load cache).next (childGate (T:=T) gates)) :=
  retypeKeptOwners (creation_context_matches_the_real_cached_child Y gates K cache h)
    (child_data_is_next_parent_data Y gates (cachedAdvance Y u K.load cache)) K.held

theorem carried_roster_has_the_actual_raw_payload (h : NativeCreationOwnerContext Y K.load) :
    (carriedRosterForCachedChild Y gates K cache h).order=K.held.order ∧
      HEq (carriedRosterForCachedChild Y gates K cache h).raw K.held.raw :=
  retyped_owners_keep_exact_bytes _ _ _

#print axioms retyped_owners_keep_exact_bytes
#print axioms actual_keepR58_sends_its_own_owner_names
#print axioms carried_roster_has_the_actual_raw_payload
end
end J6R94HeldOwnerProvider