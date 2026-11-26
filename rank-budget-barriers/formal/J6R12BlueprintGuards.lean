import J6R12BlueprintSite
import J6R10ReachablePrinted

/-! Produce the guarded active site from actual source numerical bounds.
This supplies the ready test on reachable physical hosts rather than
requiring arbitrary oversized Call records to fit in one probe field. -/
namespace J6R12Blueprint
open scoped Polynomial
open Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint
  J6R11Repack J1PPrinted

variable {f : ℤ[X]} {ell : ℕ}

def printedParams (s : ℕ) : Params (f:=f) (ell:=ell) :=
  printedShape s (fun _ _ _ => 0)

set_option exponentiation.threshold 12000 in
theorem fit_of_size (s M depth C : ℕ) (hC : C ≤ s) (hM : 0 < M)
    (bound : M ≤ C*s) (hu : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s)) :
    J9PrintedSchedule.probeCount M (stepL (Nat.clog 2 s) depth) ≤
      2^(4*Nat.clog 2 s) := by
  let a := stepL (Nat.clog 2 s) depth
  have ha : 4 ≤ a := stepL_ge_four (Nat.clog 2 s) depth hu
  have ha3 : a^3 < s :=
    (Nat.pow_le_pow_right (show 0 < a by omega) (show (3:ℕ) ≤ 1000 by decide)).trans_lt
      (dimensions_small s depth hu).1
  have ha2 : 2 ≤ a^2 := by
    calc
      2 ≤ a := by omega
      _ ≤ a*a := by simpa using Nat.mul_le_mul_left a (show 1 ≤ a by omega)
      _ = a^2 := (pow_two a).symm
  have hs : 2*a ≤ s :=
    ((Nat.mul_le_mul_right a ha2).trans_eq (Nat.pow_succ a 2).symm).trans ha3.le
  have hm : M ≤ s^2 := bound.trans
    (by simpa only [pow_two] using Nat.mul_le_mul_right s hC)
  have hdeg : J9PrintedSchedule.probeCount M a ≤ s^4 := by
    unfold J9PrintedSchedule.probeCount J9PrintedSchedule.degreeBound
    calc
      _ ≤ M*(2*a-1)+M := Nat.add_le_add_left hM _
      _ = M*((2*a-1)+1) := by ring
      _ = M*(2*a) := by congr 1; omega
      _ ≤ s^2*s := Nat.mul_le_mul hm hs
      _ = s^3 := (pow_succ s 2).symm
      _ ≤ s^4 := Nat.pow_le_pow_right (show 0<s by omega) (by decide)
  exact NativeProbeRing.printed_fit s (Nat.clog 2 s) _ (Nat.le_pow_clog (by decide) s) hdeg

theorem ready_of_size (s C : ℕ) (c : Call (PhysicalHost f ell))
    (hC : 0 < C) (hCs : C ≤ s) (hF : f.natDegree = 4*Nat.clog 2 s)
    (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (hsize : (2*epsDen)^30*C^10 ≤ Nat.clog 2 s)
    (hactive : (printedParams (f:=f) (ell:=ell) s).cutoff < c.edges)
    (hdepth : 8^c.depth*c.edges ≤ C*s)
    (hcount : c.host.edgeCount = c.edges) (degree : GoodDegree c.host (sourceDelta s))
    (tags : GoodTags c.host c.prec) :
    Ready (printedParams s) (sourceDelta s) c := by
  obtain ⟨hc,hp,hl⟩ := source_packing_conditions s c.edges c.depth hU hactive
  obtain ⟨_,hwidth,_⟩ := printed_taper_legal s c.edges C c.depth hU hC hsize hactive hdepth
  refine ⟨hactive,hcount,degree,tags,hc,hp,hl,hwidth,?_⟩
  have hM : c.edges ≤ C*s :=
    (Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)).trans hdepth
  change J9PrintedSchedule.probeCount c.edges (stepL (Nat.clog 2 s) c.depth) ≤ 2^f.natDegree
  rw [hF]
  exact fit_of_size s c.edges c.depth C hCs (Nat.zero_lt_of_lt hactive) hM hU

#print axioms fit_of_size
#print axioms ready_of_size
end J6R12Blueprint