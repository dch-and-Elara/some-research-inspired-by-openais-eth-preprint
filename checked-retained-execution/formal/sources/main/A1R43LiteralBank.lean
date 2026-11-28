import J6R14ZeroModeProbe

set_option autoImplicit false
set_option warningAsError true

/-! Literal eligible binary probe bank with zero chosen at a fixed
public index before any source tensor values. -/
namespace A1R43Literal
open scoped Classical Polynomial
noncomputable section
open Polynomial

structure EligibleBank (f : ℤ[X]) (D : ℕ) where
  word : Fin (D+1) → Fin f.natDegree → Bool
  first_zero : word 0 = (fun _=>false)
  units : ∀ p,0<p → ∀ i j,i≠j →
    IsUnit (NativeProbeRing.probe p f (word j)-NativeProbeRing.probe p f (word i))

def eligiblePrefix (f : ℤ[X]) (D q : ℕ) (fit : D+1≤2^q)
    (words : Fin (2^q)→Fin f.natDegree→Bool)
    (first : words ⟨0,pow_pos (by decide) _⟩=(fun _=>false))
    (units : ∀ p,0<p→∀ i j,i≠j→
      IsUnit (NativeProbeRing.probe p f (words j)-NativeProbeRing.probe p f (words i))) :
    EligibleBank f D where
  word i := words (Fin.castLE fit i)
  first_zero := by
    rw [show Fin.castLE fit (0:Fin (D+1))=⟨0,pow_pos (by decide) _⟩ from Fin.ext rfl,first]
  units p hp i j hn := units p hp _ _ (fun e=>hn (Fin.ext (congrArg (fun z : Fin (2^q)=>z.val) e)))

theorem eligible_first_actual_zero (f : ℤ[X]) (D p : ℕ) (bank : EligibleBank f D) :
    J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f (bank.word 0))=0 := by
  rw [bank.first_zero,J6R14ZeroMode.actual_probe_zero,map_zero]


#print axioms eligiblePrefix
#print axioms eligible_first_actual_zero
end
end A1R43Literal
