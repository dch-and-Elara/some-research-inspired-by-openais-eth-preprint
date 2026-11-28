
import J9R18CompiledChild

/-! The geometry need not be supplied by a free match oracle. On an
explicit ordered list of real wires, the original shift chart is
found by comparing the two endpoint positions in true packet seats. -/
namespace J9R18Compiled
open J8Physical
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)

def checkShift [DecidableEq Packet] (x y : Wire R) : Bool :=
  decide ((d.seat x).1 = (d.seat y).1) &&
  decide (((d.seat x).2.val : ℤ)+((L:ℤ)-1) = ((d.seat y).2.val : ℤ))

theorem checkShift_exact [DecidableEq Packet] (x y : Wire R) :
    checkShift d x y = true ↔ Shift d x y := by simp [checkShift,Shift]

def candidates (wires : List (Wire R)) : List (Bool × Wire R) :=
  wires.flatMap fun y => [(false,y),(true,y)]

theorem candidates_length (wires : List (Wire R)) :
    (candidates wires).length = 2*wires.length := by
  induction wires with
  | nil => simp [candidates]
  | cons y rest ih =>
    simp only [candidates,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem candidate_mem (wires : List (Wire R)) (all : ∀ y, y ∈ wires) (q : Bool × Wire R) :
    q ∈ candidates wires := by
  obtain ⟨b,y⟩ := q
  apply List.mem_flatMap.mpr
  refine ⟨y,all y,?_⟩
  cases b <;> simp

def scannedHit [DecidableEq Packet] (wires : List (Wire R)) (r : R) :
    Option (Bool × Wire R) :=
  (candidates wires).find? fun q => checkShift d (r,q.1) q.2

theorem scannedHit_exact [DecidableEq Packet] (e : EndpointSeating d)
    (wires : List (Wire R)) (all : ∀ y, y∈wires) (r : R) :
    scannedHit d wires r = (actualHit d r).map Subtype.val := by
  classical
  cases hs : scannedHit d wires r with
  | none =>
    have notHit : ¬Nonempty (Hit d r) := by
      intro h
      obtain ⟨hit⟩ := h
      have hw : hit.val ∈ candidates wires := candidate_mem wires all hit.val
      have hcheck : checkShift d (r,hit.val.1) hit.val.2 = true :=
        (checkShift_exact d _ _).2 hit.prop
      have hh : (candidates wires).find? (fun z => checkShift d (r,z.1) z.2) = none := hs
      have hfalse := List.find?_eq_none.mp hh hit.val hw
      rw [hcheck] at hfalse
      contradiction
    simp [actualHit,notHit]
  | some q =>
    have hh : (candidates wires).find? (fun z => checkShift d (r,z.1) z.2) = some q := hs
    have hcheck := List.find?_some hh
    rw [actualHit_some d e ((checkShift_exact d _ _).1 hcheck)]
    rfl

/-- Read the true old nonpin owner and port by the supplied column incidence
bijection, not by another search or optimisation oracle. -/
def scannedOldPort [DecidableEq Packet] (wires : List (Wire R)) (r : R) :
    Option (Bool × Sigma P) :=
  (scannedHit d wires r).bind fun q =>
    (d.column q.2).elim (fun _ => none) (fun v => some (q.1,v))

theorem scannedOldPort_exact [DecidableEq Packet] (e : EndpointSeating d)
    (wires : List (Wire R)) (all : ∀ y, y∈wires) (r : R) :
    scannedOldPort d wires r =
      (actualHit d r).map (fun h => (h.val.1,hitColumn d e h)) := by
  unfold scannedOldPort
  rw [scannedHit_exact d e wires all r]
  cases h : actualHit d r with
  | none => rfl
  | some w => simp [hitColumn_eq d e w]

#print axioms checkShift_exact
#print axioms candidates_length
#print axioms scannedHit_exact
#print axioms scannedOldPort_exact

end J9R18Compiled
