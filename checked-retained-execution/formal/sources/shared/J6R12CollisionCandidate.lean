import J6R12CollisionBits
import J6R11CollisionCostSelect

/-!
# Candidate comparisons on cached little-endian registers

This loop is parametric in a metered evaluator of a candidate tape.
The bridge theorem composes it with any exact concrete score evaluator.
It does not use an integer comparison or unpack a candidate into a Nat.
-/

namespace J6R12CollisionCandidate
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionBits
open scoped Classical

structure Entry where
  label : List Bool
  score : List Bool

def scanFrom (w b : ℕ) (eval : List Bool → Meter (List Bool)) (best : Entry) :
    List (List Bool) → Meter Entry
  | [] => ⟨best,0⟩
  | lab::ls =>
    let s := eval lab
    let q := compareBits s.result best.score
    let keep := if q.result then ⟨lab,s.result⟩ else best
    let next := scanFrom w b eval keep ls
    ⟨next.result,s.steps+q.steps+next.steps+2*w+2*b+8⟩

def scanMenu (w b : ℕ) (eval : List Bool → Meter (List Bool))
    (first : List Bool) (rest : List (List Bool)) : Meter Entry :=
  let s := eval first
  let q := scanFrom w b eval ⟨first,s.result⟩ rest
  ⟨q.result,s.steps+q.steps+2*w+2*b+8⟩

theorem scanFrom_exact {A : Type*} (w b g : ℕ)
    (code : A → List Bool) (score : A → ℕ)
    (eval : List Bool → Meter (List Bool))
    (ha : ∀ a, (eval (code a)).result.length=w ∧
      bitsValue (eval (code a)).result=score a ∧ (eval (code a)).steps≤g)
    (as : List A) (a : A) (buf : List Bool)
    (hb : buf.length=w) (hv : bitsValue buf=score a) :
    let x := scanFrom w b eval ⟨code a,buf⟩ (as.map code)
    let y := J6R11CollisionCostSelect.scan (a,score a) (as.map (fun j => (j,score j)))
    x.result.label=code y.1 ∧ x.result.score.length=w ∧
      bitsValue x.result.score=y.2 ∧ x.steps≤(g+12*w+2*b+8)*as.length := by
  induction as generalizing a buf with
  | nil => simp [scanFrom,J6R11CollisionCostSelect.scan,hb,hv]
  | cons l ls ih =>
    let s := eval (code l)
    let q := compareBits s.result buf
    obtain ⟨hs,hsval,hsc⟩ := ha l
    have H := compareBits_exact s.result buf (hs.trans hb.symm)
    change (q.result=true ↔ bitsValue s.result<bitsValue buf) ∧ q.steps=10*s.result.length at H
    have qh : q.result=true ↔ score l<score a := H.1.trans (by rw [show bitsValue s.result=score l from hsval,hv])
    have qc : q.steps=10*w := H.2.trans (by rw [show s.result.length=w from hs])
    simp only [List.map_cons,List.length_cons,scanFrom,J6R11CollisionCostSelect.scan]
    change (scanFrom w b eval (if q.result then ⟨code l,s.result⟩ else ⟨code a,buf⟩) (ls.map code)).result.label=code (J6R11CollisionCostSelect.scan (if score l<score a then (l,score l) else (a,score a)) (ls.map (fun j => (j,score j)))).1 ∧
      (scanFrom w b eval (if q.result then ⟨code l,s.result⟩ else ⟨code a,buf⟩) (ls.map code)).result.score.length=w ∧
      bitsValue (scanFrom w b eval (if q.result then ⟨code l,s.result⟩ else ⟨code a,buf⟩) (ls.map code)).result.score=(J6R11CollisionCostSelect.scan (if score l<score a then (l,score l) else (a,score a)) (ls.map (fun j => (j,score j)))).2 ∧
      s.steps+q.steps+(scanFrom w b eval (if q.result then ⟨code l,s.result⟩ else ⟨code a,buf⟩) (ls.map code)).steps+2*w+2*b+8≤(g+12*w+2*b+8)*(ls.length+1)
    by_cases hh : score l<score a
    · simp only [if_pos hh,if_pos (qh.mpr hh)]
      obtain ⟨h1,h2,h3,h4⟩ := ih l s.result hs hsval
      refine ⟨h1,h2,h3,?_⟩
      rw [qc,Nat.mul_succ]
      change s.steps≤g at hsc
      omega
    · simp only [if_neg hh,if_neg (qh.not.mpr hh)]
      obtain ⟨h1,h2,h3,h4⟩ := ih a buf hb hv
      refine ⟨h1,h2,h3,?_⟩
      rw [qc,Nat.mul_succ]
      change s.steps≤g at hsc
      omega

theorem scanMenu_exact {A : Type*} (w b g : ℕ)
    (code : A → List Bool) (score : A → ℕ)
    (eval : List Bool → Meter (List Bool))
    (ha : ∀ a, (eval (code a)).result.length=w ∧
      bitsValue (eval (code a)).result=score a ∧ (eval (code a)).steps≤g)
    (first : A) (rest : List A) :
    let x := scanMenu w b eval (code first) (rest.map code)
    let y := J6R11CollisionCostSelect.minimumEntry score first rest
    x.result.label=code y.1 ∧ x.result.score.length=w ∧
      bitsValue x.result.score=score y.1 ∧
      x.steps≤(g+12*w+2*b+8)*(rest.length+1) := by
  let s := eval (code first)
  obtain ⟨h1,h2,h3,h4⟩ := scanFrom_exact w b g code score eval ha rest first s.result
    (ha first).1 (ha first).2.1
  unfold scanMenu
  refine ⟨h1,h2,h3.trans (J6R11CollisionCostSelect.minimumEntry_cached score first rest),?_⟩
  rw [Nat.mul_succ]
  have ht : s.steps≤g := (ha first).2.2
  change s.steps+(scanFrom w b eval ⟨code first,s.result⟩ (rest.map code)).steps+2*w+2*b+8≤_
  omega

#print axioms scanFrom_exact
#print axioms scanMenu_exact

end J6R12CollisionCandidate
