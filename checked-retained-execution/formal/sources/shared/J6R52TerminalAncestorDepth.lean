import J6R52TerminalFreshCore
import J6R33StatefulArithmeticPageProjection
import J6R21AncestorHistory

/-! An old generated Page need not carry a separately supplied depth
word for the leaf. Its genuine fixed prefix gives that depth. For an
isolated old vertex there is no precursor body, but its existing
empty-wire Page evaluator is exactly insensitive to depth and fee. -/
namespace J6R52Terminal
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12
open J6R15ModeCost J6R21Ancestor J6R33StatefulArithmeticPage J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R22Active J6R24MeteredRecursion
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000
set_option maxRecDepth 3000
set_option Elab.async false

def readDepthPrefix : List Bool→Meter (Option ℕ)
  | [] => ⟨none,2⟩
  | true::_ => ⟨some 0,3⟩
  | false::rest =>
    let read := readDepthPrefix rest
    ⟨read.result.map (·+1),read.steps+4⟩

theorem real_depth_prefix (depth : ℕ) (suffix : List Bool) :
    readDepthPrefix (List.replicate depth false++true::suffix)=⟨some depth,4*depth+3⟩ := by
  induction depth with
  | zero => rfl
  | succ d ih =>
    simp only [List.replicate_succ,List.cons_append,readDepthPrefix,ih,Option.map_some]
    congr 1

def requestDepth {w : ℕ} : List (WireRequest w)→Meter (Option ℕ)
  | []=>⟨some 0,3⟩
  | x::_ =>
    let out := readDepthPrefix x.ancestry
    ⟨out.result,out.steps+3⟩

theorem request_depth_from_true_trace {f : ℤ[X]} {ell w : ℕ}
    {origin cur : Point f ell} (tr : Trace origin cur)
    (seed : PortAt origin→List Bool)
    (starts : ∀ p,∃ rest,seed p=true::rest)
    (u : PortAt cur) (edgeWord : Word w) (rest : List (WireRequest w)) :
    requestDepth (⟨edgeWord,tr.literal seed u⟩::rest)=⟨some tr.depth,4*tr.depth+6⟩ := by
  obtain ⟨s,hs⟩ := starts (tr.back u)
  rw [tr.literal_exact,hs]
  unfold requestDepth
  dsimp only
  rw [real_depth_prefix]

theorem empty_leaf_page_ignores_depth {f : ℤ[X]} {p ell key prec tw bw page : ℕ}
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page) (keyWord : Word key) (pageWord : Word page)
    (a b : ℕ) (bits : List Bool) :
    readPage hf F pos keyWord pageWord a [] bits B =
      readPage hf F pos keyWord pageWord b [] bits B := by
  unfold readPage consumePage
  dsimp only
  cases seen : (locate keyWord B.records).result with
  | none => rfl
  | some record =>
    dsimp only
    cases arrived : (locate pageWord record.payload.pages).result with
    | none => rfl
    | some present =>
      dsimp only
      rfl

#print axioms real_depth_prefix
#print axioms request_depth_from_true_trace
#print axioms empty_leaf_page_ignores_depth
end J6R52Terminal
