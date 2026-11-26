import J6R12BlueprintFactory
import J6R12BlueprintGuards
import J6R12RepackGenerated
import J6R11BlueprintReach

/-! Invariants of the actual dependent packet factory at arbitrary
generated depth. The source size/field guards are checked on exactly
the reachable active calls; the raw-call fallback branch cannot occur
along a genuine run from a valid root. -/
namespace J6R12Blueprint
open scoped Classical Polynomial
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
  J6R11Blueprint J6R11Repack J6R12Repack J1PPrinted

variable {f : ℤ[X]} {ell : ℕ}

structure RootBounds (s C : ℕ) (f : ℤ[X]) : Prop where
  coefficient : f.natDegree = 4*Nat.clog 2 s
  constPos : 0 < C
  constSmall : C ≤ s
  widthPos : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s)
  size : (2*epsDen)^30*C^10 ≤ Nat.clog 2 s

structure Stable (s C : ℕ) (c : Call (PhysicalHost f ell)) : Prop where
  edgeCount : c.host.edgeCount = c.edges
  degree : GoodDegree c.host (sourceDelta s)
  tags : GoodTags c.host c.prec
  sizeByDepth : 8^c.depth*c.edges ≤ C*s

theorem stable_root (s C : ℕ) (r : Call (PhysicalHost f ell)) (h0 : r.depth = 0)
    (edge : r.host.edgeCount = r.edges) (degree : GoodDegree r.host (sourceDelta s))
    (tags : GoodTags r.host r.prec) (size : r.edges ≤ C*s) : Stable s C r :=
  ⟨edge,degree,tags,by simpa only [h0,pow_zero,one_mul] using size⟩

variable {s C : ℕ} (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))

noncomputable abbrev N := shape (printedParams s) (sourceDelta s) sel
noncomputable abbrev Childs := children (printedParams s) (sourceDelta s) sel
noncomputable abbrev Plan := nativePlan (N sel) (Childs sel)

include cfg in
theorem getReady {c : Call (PhysicalHost f ell)} (hc : Stable s C c)
    (ha : (printedParams (f:=f) (ell:=ell) s).cutoff < c.edges) :
    Ready (printedParams s) (sourceDelta s) c :=
  ready_of_size s C c cfg.constPos cfg.constSmall cfg.coefficient cfg.widthPos cfg.size ha
    hc.sizeByDepth hc.edgeCount hc.degree hc.tags

set_option maxHeartbeats 3500000 in
include cfg in
theorem stable_step {c : Call (PhysicalHost f ell)} (hc : Stable s C c)
    (w : LiveAddress (N sel) c) : Stable s C ((Plan sel).child c w) := by
  let S := printedParams (f:=f) (ell:=ell) s
  let d := getReady cfg hc w.property
  let t := w.val.1
  let p := registerPrecision S c t
  let i := centerIndex d t
  let β := siteTuple sel d w.val
  let g := w.val.2.2.2
  let z := w.val.2.1
  let new := packetOfSite sel d t z β g
  have hincrease : c.prec ≤ p :=
    (child_monotone c.prec _ _ _ t.val (Nat.zero_lt_of_lt d.active)).le
  have hM : 0 < c.host.edgeCount := d.edgeCount.symm ▸ Nat.zero_lt_of_lt d.active
  have hnew := generated_invariants (H:=c.host) (packing sel d) i (centerNonzero t) rfl c.prec p
    (J6R10Integral.box_two_nil p f ell) (sampleNode S f ell c d.fit t z) β g
    (sourceDelta s) (Fintype.card_fin 64) hM d.degree d.packetDegree d.tags hincrease
  change GoodDegree new (sourceDelta s) ∧ GoodTags new p ∧
    32*new.edgeCount ≤ 3*c.host.edgeCount ∧ new.edgeCount < c.host.edgeCount at hnew
  have hcard : 8*new.edgeCount ≤ c.edges := by
    have hb := hnew.2.2.1
    rw [d.edgeCount] at hb
    omega
  rw [show (Plan sel).child c w = ⟨new,c.depth+1,new.edgeCount,p⟩ from child_exact sel d w.val]
  refine ⟨rfl,hnew.1,hnew.2.1,?_⟩
  change 8^(c.depth+1)*new.edgeCount ≤ C*s
  rw [pow_succ,mul_assoc]
  exact (Nat.mul_le_mul_left _ hcard).trans hc.sizeByDepth

include cfg in
theorem stable_reachable {r c : Call (PhysicalHost f ell)}
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) : Stable s C c := by
  induction h with
  | reflexive => exact hr
  | step w _ ih => exact ih (stable_step cfg sel hr w)

include cfg in
theorem ready_reachable {r c : Call (PhysicalHost f ell)}
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r)
    (ha : (printedParams (f:=f) (ell:=ell) s).cutoff < c.edges) :
    Ready (printedParams s) (sourceDelta s) c :=
  getReady cfg (stable_reachable cfg sel h hr) ha

theorem positive_at_native (r : Call (PhysicalHost f ell))
    [DecidableEq (Envelope (N sel) (Childs sel) r)] :
    PositiveData (N sel) (Childs sel) r :=
  fun c _ _ t m => weightAt_pos _ _ sel c t m

noncomputable def sourceBlueprint (r : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N sel) (Childs sel) r)] :
    Blueprint (paddedShape (N sel) (Childs sel) r) f ell :=
  paddedBlueprint (N sel) (Childs sel) r (positive_at_native sel r) f ell (physicalEntries hf)

#print axioms stable_root
#print axioms getReady
#print axioms stable_step
#print axioms stable_reachable
#print axioms ready_reachable
#print axioms sourceBlueprint
end J6R12Blueprint