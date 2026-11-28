import J6R16ModeCostUniform

/-! The actual R15 stream meter at a selected native packet site,
with the weight and precision tape given. The fuel counts only as a
proof-side stopping witness; the algorithm emits until its halt pulse. -/
namespace J6R16ModeCost
open scoped Polynomial Classical
open AOracleMachineTime
open J1PPrinted J6ActiveRun J6R10Reachable J6R12Blueprint J6R11Blueprint J6R15ModeCost

structure SiteTape {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
    (sel : Selector S Δ) {c : Call (PhysicalHost f ell)}
    (d : Ready S Δ c) (t : Center S c) (q : ℕ) where
  modes : List (NativeRoster sel d t)
  nodup : modes.Nodup
  allModes : ∀ m,m∈modes
  words : List (Word q)
  precision : Word q
  weightMeaning : words.map Word.val=modes.map modeWeight
  precisionMeaning : precision.val=registerPrecision S c t

def measuredSite {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
    {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
    {d : Ready S Δ c} {t : Center S c} (I : SiteTape sel d t q) : ℕ :=
  let xs := strictTuples (I.modes.map modeWeight) (registerPrecision S c t)
  let z := start I.words I.precision
  z.steps+match z.result with
    | .again st => (collect I.words.length (xs.length+1) st).steps
    | .halt => 0
    | .emit _ _ => 0

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
include cfg

theorem achievable_tape_width
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (d : Ready S (sourceDelta s) c) (t : Center S c) :
    Nonempty (SiteTape sel d t (uniformWidth s C)) := by
  let ms := (Finset.univ : Finset (NativeRoster sel d t)).toList
  let p := registerPrecision S c t
  let q := uniformWidth s C
  have hp : p<2^q := raw_width_fits s C _ (register_size_bound cfg sel h hr hzero hroot d.active t)
  refine ⟨⟨ms,Finset.nodup_toList _,by intro m; simp [ms],ms.map (fun m=>word (q:=q) (modeWeight m)),
    word (q:=q) p,?_,word_val hp⟩⟩
  rw [List.map_map]
  apply List.map_congr_left
  intro m _
  exact word_val ((modeWeight_bounds m).2.trans hp)

theorem measured_site_bound
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (d : Ready S (sourceDelta s) c) (t : Center S c)
    (I : SiteTape sel d t (uniformWidth s C)) :
    measuredSite I≤uniformFee s C*2^(depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  let p := registerPrecision S c t
  let q := uniformWidth s C
  let xs := strictTuples (I.modes.map modeWeight) p
  let E := depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth
  have hQ : 0<q := by unfold q uniformWidth; omega
  have hp : 0<p := register_positive d t
  obtain ⟨st,hStart,_,_,_,hTime⟩ :=
    roster_paid hQ hp I.modes I.words I.precision I.weightMeaning I.precisionMeaning
  have hTuples : xs.length≤2^E :=
    tuple_depth_bound cfg sel h hr hzero hroot d t I.modes I.nodup I.allModes
  have hN : I.words.length≤rosterSize s C := by
    have H := congrArg List.length I.weightMeaning
    simp only [List.length_map] at H
    rw [H]
    exact roster_size_bound cfg sel h hr hzero hroot d t I.modes I.nodup I.allModes
  unfold measuredSite
  dsimp only
  rw [hStart]
  exact hTime.trans ((fee_times_depth xs.length q I.words.length E hTuples).trans
    (Nat.mul_le_mul_right _ (localFee_mono q hN)))

#print axioms achievable_tape_width
#print axioms measured_site_bound
end J6R16ModeCost

