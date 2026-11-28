import J6R19RetainedWords
import J6R18ChildWriteBytes

/-! Sequential ingress for an already emitted old entry frame.
The exactness theorem is on valid creation-time frames; this reader
does not certify an arbitrary malformed byte string or find a handle. -/
namespace J6R19Retained
open A1R10 A1R12 AOracleMachineTime J6R18ChildWrite

theorem lowBits_prefix (a b : List Bool) : lowBits a.length (a++b)=a := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [lowBits,ih]

def cutWord (k : ℕ) (bs : List Bool) : Meter (Word k × List Bool) :=
  let z := scanWidth k bs
  ⟨(⟨z.result,(congrArg List.length (scanWidth_exact k bs).1).trans (lowBits_len k bs)⟩,bs.drop k),
    z.steps+2*k+2⟩

def cutWordFee (k : ℕ) := 6*k+3

theorem cutWord_exact {k : ℕ} (w : Word k) (suffix : List Bool) :
    (cutWord k (w.val++suffix)).result=(w,suffix) ∧
      (cutWord k (w.val++suffix)).steps=cutWordFee k := by
  obtain ⟨hv,hc⟩ := scanWidth_exact k (w.val++suffix)
  have hV : lowBits k (w.val++suffix)=w.val := by
    simpa only [w.property] using lowBits_prefix w.val suffix
  have hS : (w.val++suffix).drop k=suffix := by
    simpa only [w.property] using List.drop_left (l₁:=w.val) (l₂:=suffix)
  constructor
  · exact Prod.ext (Subtype.ext (hv.trans hV)) hS
  · change (scanWidth k (w.val++suffix)).steps+2*k+2=_
    rw [hc,cutWordFee]
    omega

def cutMany {A : Type*} (cut : List Bool→Meter (A×List Bool)) (stamp : ℕ) :
    (n : ℕ)→List Bool→Meter ({v : List A // v.length=n}×List Bool)
  | 0,bs => ⟨(⟨[],rfl⟩,bs),2⟩
  | n+1,bs =>
    let h := cut bs
    let t := cutMany cut stamp n h.result.2
    ⟨(⟨h.result.1::t.result.1.val,by simp only [List.length_cons,t.result.1.property]⟩,t.result.2),
      h.steps+t.steps+stamp+4⟩

theorem cutMany_exact {A : Type*} (cut : List Bool→Meter (A×List Bool)) (stamp fee : ℕ)
    (encode : A→List Bool)
    (h : ∀ v bs,(cut (encode v++bs)).result=(v,bs) ∧ (cut (encode v++bs)).steps=fee)
    (vs : List A) (suffix : List Bool) :
    let z := cutMany cut stamp vs.length (vs.flatMap encode++suffix)
    z.result.1.val=vs ∧ z.result.2=suffix ∧ z.steps=vs.length*(fee+stamp+4)+2 := by
  induction vs with
  | nil => simp [cutMany]
  | cons v vs ih =>
    obtain ⟨hV,hS,hC⟩ := ih
    let r := vs.flatMap encode++suffix
    obtain ⟨h1,h2⟩ := h v r
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,cutMany,r,h1,h2,hV,hS,hC,true_and]
    rw [Nat.succ_mul vs.length]
    omega

def rawU {p : ℕ} {ws : List (Word p)} (u : UBlock ws) : List Bool :=
  u.val.flatMap Subtype.val

def cutU {p : ℕ} (ws : List (Word p)) (bs : List Bool) : Meter (UBlock ws × List Bool) :=
  cutMany (cutWord p) p ws.length bs

def cutUFee (e p : ℕ) := e*(cutWordFee p+p+4)+2

theorem cutU_exact {p : ℕ} {ws : List (Word p)} (u : UBlock ws) (suffix : List Bool) :
    (cutU ws (rawU u++suffix)).result=(u,suffix) ∧
      (cutU ws (rawU u++suffix)).steps=cutUFee ws.length p := by
  obtain ⟨hu,hr,hc⟩ := cutMany_exact (cutWord p) p (cutWordFee p) Subtype.val
    cutWord_exact u.val suffix
  rw [u.property] at hu hr hc
  exact ⟨Prod.ext (Subtype.ext hu) hr,hc⟩

def cutUV {p : ℕ} (ws : List (Word p)) (ell : ℕ) (bs : List Bool) :
    Meter (UVBlock ws ell × List Bool) :=
  cutMany (cutU ws) (ws.length*p) ell bs

def cutUVFee (e ell p : ℕ) := ell*(cutUFee e p+e*p+4)+2

theorem cutUV_exact {p ell : ℕ} {ws : List (Word p)} (v : UVBlock ws ell) (suffix : List Bool) :
    (cutUV ws ell (flattenEntry v++suffix)).result=(v,suffix) ∧
      (cutUV ws ell (flattenEntry v++suffix)).steps=cutUVFee ws.length ell p := by
  obtain ⟨hu,hr,hc⟩ := cutMany_exact (cutU ws) (ws.length*p) (cutUFee ws.length p) rawU
    cutU_exact v.val suffix
  rw [v.property] at hu hr hc
  exact ⟨Prod.ext (Subtype.ext hu) hr,hc⟩

def readOldFrame {p : ℕ} (ws : List (Word p)) (ell t : ℕ) (bs : List Bool) :
    Meter (Word t × UVBlock ws ell × List Bool) :=
  let h := cutWord t bs
  let v := cutUV ws ell h.result.2
  ⟨(h.result.1,v.result.1,v.result.2),h.steps+v.steps+4⟩

def ingressFee (e ell p t : ℕ) := cutWordFee t+cutUVFee e ell p+4

theorem readOldFrame_exact {p ell t : ℕ} {ws : List (Word p)} (tag : J6R15ModeCost.Word t)
    (v : UVBlock ws ell) (suffix : List Bool) :
    let z := readOldFrame ws ell t ((writeEntry tag v).result++suffix)
    z.result=(⟨tag.bits,tag.size⟩,v,suffix) ∧ z.steps=ingressFee ws.length ell p t := by
  obtain ⟨h1,h2⟩ := cutWord_exact (⟨tag.bits,tag.size⟩ : Word t) (flattenEntry v++suffix)
  obtain ⟨h3,h4⟩ := cutUV_exact v suffix
  simp only [readOldFrame,writeEntry,List.append_assoc,h1,h2,h3,h4,ingressFee,true_and]

#print axioms lowBits_prefix
#print axioms cutWord_exact
#print axioms cutMany_exact
#print axioms cutU_exact
#print axioms cutUV_exact
#print axioms readOldFrame_exact
end J6R19Retained


