import J6R21AncestorRegistry
import J6R12BlueprintReach

/-! The stored creation stamp is not the receiving precision field
of a recursive child header. An old entry copies the immutable
creator and creation-width words verbatim from its located retained
record. A genuinely new packet is stamped at its source creation
site and precision. This prices the tag words, not Gate evaluation
or unrestricted generation of old vertex references. -/
namespace J6R26DescriptorTree
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R10Repack J6R11Blueprint P11FullPacking J6R9PacketScopes

structure Stamp (ownerWidth timeWidth : ℕ) where
  creator : Word ownerWidth
  created : Word timeWidth

def duplicateWord {w : ℕ} (x : Word w) : Meter (Word w) :=
  let op := copyBytes x.bits
  ⟨⟨op.result,by change (copyBytes x.bits).result.length=w; rw [copyBytes_exact]; exact x.size⟩,
    op.steps+3⟩

theorem duplicate_word_exact {w : ℕ} (x : Word w) : duplicateWord x=⟨x,3*w+4⟩ := by
  have hv : (duplicateWord x).result=x := by
    change Word.mk (copyBytes x.bits).result _=x
    simp only [copyBytes_exact]
  have ht : (duplicateWord x).steps=3*w+4 := by
    change (copyBytes x.bits).steps+3=_
    rw [copyBytes_exact]
    change 3*x.bits.length+1+3=_
    rw [x.size]
  cases h : duplicateWord x with
  | mk result steps =>
    rw [h] at hv ht
    change result=x at hv
    change steps=3*w+4 at ht
    rw [hv,ht]

def duplicateStamp {w b : ℕ} (s : Stamp w b) : Meter (Stamp w b) :=
  let o := duplicateWord s.creator
  let p := duplicateWord s.created
  ⟨⟨o.result,p.result⟩,o.steps+p.steps+4⟩

theorem duplicate_stamp_exact {w b : ℕ} (s : Stamp w b) : duplicateStamp s=⟨s,3*w+3*b+12⟩ := by
  cases s with
  | mk c p =>
    simp only [duplicateStamp,duplicate_word_exact]
    congr 1
    omega

def keptStamp {w b : ℕ} (bank : List (RefRow w (Stamp w b))) (id : Word w) :
    Meter (Option (Stamp w b)) :=
  let rc := locate id bank
  match rc.result with
  | none => ⟨none,rc.steps+4⟩
  | some s =>
    let cp := duplicateStamp s
    ⟨some cp.result,rc.steps+cp.steps+4⟩

theorem kept_stamp_exact {w b : ℕ} (bank : List (RefRow w (Stamp w b))) (id : Word w)
    (stamp : Stamp w b) (found : (⟨id,stamp⟩ : RefRow w (Stamp w b))∈bank)
    (unique : ∀ row∈bank,row.address = id → row.payload = stamp) :
    (keptStamp bank id).result=some stamp ∧
      (keptStamp bank id).steps=(locate id bank).steps+3*w+3*b+16 := by
  unfold keptStamp
  dsimp only
  rw [locate_hit id stamp bank found unique]
  change some (duplicateStamp stamp).result=some stamp ∧
    (locate id bank).steps+(duplicateStamp stamp).steps+4=_
  rw [duplicate_stamp_exact]
  exact ⟨rfl,by change (locate id bank).steps+(3*w+3*b+12)+4=_; omega⟩

def writeStamp {w b : ℕ} (bank : List (RefRow w (Stamp w b))) (receive : Word b)
    (request : Word w⊕Word w) : Meter (Option (Stamp w b)) :=
  match request with
  | .inl old => keptStamp bank old
  | .inr creator =>
    let out := duplicateStamp (⟨creator,receive⟩ : Stamp w b)
    ⟨some out.result,out.steps+4⟩

section Physical
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {f : ℤ[X]} {ell a p w b : ℕ}
variable {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
variable (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable (nil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
variable (oldFile : EntryFile f ell N) (β : Mode i p P.mask →₀ ℕ) (g : G)

set_option maxHeartbeats 2900000 in
theorem actual_retained_tag_word
    (V : Old (atGroup P i) g) (receiving : Word b)
    (bank : List (RefRow w (Stamp w b))) (lookup : Word w) (stamp : Stamp w b)
    (oldTag : stamp.created.val=(oldFile V.val).created)
    (atRow : (⟨lookup,stamp⟩ : RefRow w (Stamp w b))∈bank)
    (unique : ∀ row∈bank,row.address = lookup → row.payload = stamp) :
    let C := actualPacketHost P i ht hv p nil z oldFile β g
    let out := writeStamp bank receiving (.inl lookup)
    out.result=some stamp ∧ stamp.created.val=(C.file (.inl V)).created ∧
      out.steps=(locate lookup bank).steps+3*w+3*b+16 := by
  have ⟨reply,fee⟩ := kept_stamp_exact bank lookup stamp atRow unique
  exact ⟨reply,oldTag,fee⟩

set_option maxHeartbeats 2600000 in
theorem actual_generated_tag_word {K : Page a P.copies G}
    (receiving : Word b) (recv : receiving.val=p) (owner : Word w)
    (bank : List (RefRow w (Stamp w b))) :
    let C := actualPacketHost P i ht hv p nil z oldFile β g
    let out := writeStamp bank receiving (.inr owner)
    let stamp : Stamp w b := ⟨owner,receiving⟩
    out.result=some stamp ∧ stamp.created.val=(C.file (.inr K)).created ∧
      out.steps=3*w+3*b+16 := by
  change (some (duplicateStamp (⟨owner,receiving⟩ : Stamp w b)).result=some ⟨owner,receiving⟩)
    ∧ receiving.val=p ∧ (duplicateStamp (⟨owner,receiving⟩ : Stamp w b)).steps+4=3*w+3*b+16
  rw [duplicate_stamp_exact]
  exact ⟨rfl,recv,by change 3*w+3*b+12+4=_; omega⟩
end Physical

#print axioms duplicate_stamp_exact
#print axioms kept_stamp_exact
#print axioms actual_retained_tag_word
#print axioms actual_generated_tag_word
end J6R26DescriptorTree



