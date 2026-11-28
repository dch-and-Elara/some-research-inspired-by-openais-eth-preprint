import J6R49LiveSiteTape

/-! The selected source tape and its monic register frame justify the
mode-region budget, together with the immutable visible payload pages.
The theorem accepts a stack observation, not a proof that a given
interpreter realizes every such observation or accounts for scratch. -/
namespace J6R49LiveBits
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R16ModeCost J6R15ModeCost A1R10

set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

structure NativeSuspension (x : Call (PhysicalHost f ell)) where
  ready : Ready S (sourceDelta s) x
  center : Center S x
  q : ℕ
  fitsWord : q≤uniformWidth s C
  input : SiteTape sel ready center q
  state : J6R15ModeCost.State q
  stateFit : state.wellFormed input.words.length
  frame : J6R24MeteredRecursion.Frame f (registerPrecision S x center)
  outer : UVBlock frame.words ell
  inner : UVBlock frame.words ell

def NativeSuspension.measure {x : Call (PhysicalHost f ell)}
    (m : NativeSuspension (C:=C) (sel:=sel) x) : Suspension (s:=s) x :=
  ⟨m.ready.active,m.center,m.q,m.input.words.length,m.state,m.stateFit,
    m.frame.words,m.outer,m.inner⟩

variable {cfg : RootBounds s C f} {hf : f.Monic} {T : Prepared cfg sel r hf}

theorem selected_tape_pages_and_modes_bound
    (born : Births T key prec tw bw page) (initial : PageBank f ell key prec tw bw page)
    (U : ℕ) (hRows : AllExactPages born)
    (pageFit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
      let e := (born p w).job.immutable.payload.payload
      ∀ y ∈ e.pages, (originPayload y.payload).length≤U)
    (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (observed : {x : Call (PhysicalHost f ell)} → Path sel r x →
      Option (NativeSuspension (C:=C) (sel:=sel) x))
    (p : Path sel r c) :
    residentAtlasBits (stackBank born initial p) +
        liveModeBits (fun u => (observed u).map NativeSuspension.measure) p ≤
      residentAtlasBits initial + (96*r.edges/29)*(page+U) +
        ((pathLimit s C+1)*frameBase (uniformWidth s C) (rosterSize s C) +
          (32*r.edges/29)*frameSlope s C ell f.natDegree) := by
  apply Nat.add_le_add (scoped_generated_literal_page_bits born initial U hRows pageFit p)
  apply live_suspended_modes_geometric cfg T.rootStable hzero hroot
  intro x u m hu
  cases h : observed u with
  | none => simp only [h,Option.map_none] at hu
            cases hu
  | some now =>
    simp only [h,Option.map_some,Option.some.injEq] at hu
    subst m
    exact ⟨now.fitsWord,real_site_tape_width cfg T.rootStable hzero hroot
      u.reached now.ready now.center now.input,(now.frame.natDegree hf).le⟩

#print axioms selected_tape_pages_and_modes_bound
end J6R49LiveBits


