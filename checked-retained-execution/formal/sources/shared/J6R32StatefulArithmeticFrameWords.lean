import J6R32StatefulArithmeticCore
import A1R10Readout

/-! The canonical rectangular buffers are uniquely determined by their
decoded U/V value, including the physical bit contents. Equality here
is a proof, not an uncharged word comparison in the runtime. -/
namespace J6R32StatefulArithmetic
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 J6R22Active J6R24MeteredRecursion
open Polynomial

private theorem bits_inj (x y : List Bool) (len : x.length=y.length)
    (h : bitsValue x=bitsValue y) : x=y := by
  induction x generalizing y with
  | nil => exact (List.length_eq_zero_iff.mp len.symm).symm
  | cons a x ih =>
    cases y with
    | nil => simp at len
    | cons b y =>
      rw [bitsValue,bitsValue] at h
      have ha : a.toNat≤1 := by cases a <;> decide
      have hb : b.toNat≤1 := by cases b <;> decide
      have hhN : a.toNat=b.toNat := by omega
      have hh : a=b := by cases a <;> cases b <;> simp_all
      subst b
      exact congrArg (List.cons a) (ih y (by simpa only [List.length_cons,Nat.succ.injEq] using len) (by omega))

theorem bitWord_injective (p : ℕ) : Function.Injective (@wordRead p) := by
  intro a b he
  have ha : (wordRead a).val=bitsValue a.val :=
    ZMod.val_natCast_of_lt (by simpa only [a.property] using bitsValue_lt a.val)
  have hb : (wordRead b).val=bitsValue b.val :=
    ZMod.val_natCast_of_lt (by simpa only [b.property] using bitsValue_lt b.val)
  exact Subtype.ext (bits_inj _ _ (a.property.trans b.property.symm)
    (ha.symm.trans ((congrArg ZMod.val he).trans hb)))

theorem at_scan {A : Type*} (g : Gates A) (xs : List A) (j : ℕ) (hj : j<xs.length) :
    (scanWord g j xs).result=xs[j] := by
  rw [(scanWord_exact g xs j).1]
  simp only [List.getD_eq_getElem?_getD,getElem?_pos xs j hj,Option.getD_some]

theorem physical_scan {p ell : ℕ} {fw : List (Word p)} (hp : 0<p)
    (x : UVBlock fw ell) (j : ℕ) (hj : j<x.val.length)
    (i : ℕ) (hi : i<x.val[j].val.length) :
    (uvScan hp x i j).result=x.val[j].val[i] := by
  unfold uvScan
  dsimp only
  rw [at_scan (uGates hp fw) x.val j hj,at_scan (wordOps p hp).toGates x.val[j].val i hi]

theorem box_words_injective {p ell : ℕ} {fw : List (Word p)} (hp : 0<p)
    (mono : (Modulus p hp fw).Monic) (deg : (Modulus p hp fw).natDegree=fw.length) :
    Function.Injective (uvRead hp fw ell) := by
  intro x y h
  apply Subtype.ext
  apply List.ext_getElem (x.property.trans y.property.symm)
  intro j hj hx
  apply Subtype.ext
  apply List.ext_getElem (x.val[j].property.trans y.val[j].property.symm)
  intro i hi hy
  let ii : Fin fw.length := ⟨i,(x.val[j].property ▸ hi)⟩
  let jj : Fin ell := ⟨j,(x.property ▸ hj)⟩
  have hxR := uvScan_native hp x ii jj mono deg
  have hyR := uvScan_native hp y ii jj mono deg
  rw [h,←hyR] at hxR
  exact bitWord_injective p (by
    change wordRead (uvScan hp x i j).result=wordRead (uvScan hp y i j).result at hxR
    rw [physical_scan hp x j hj i hi,physical_scan hp y j hx i hy] at hxR
    exact hxR)

theorem frame_words_injective {f : ℤ[X]} {p ell : ℕ} (hf : f.Monic) (F : Frame f p) :
    Function.Injective (F.decode (ell:=ell)) := by
  letI : Fact (1 < (2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) F.hp.ne'⟩
  have hF : (NativeProbeRing.liftPoly p f).Monic := hf.map _
  have hm : (Modulus p F.hp F.words).Monic := F.exactMod.symm ▸ hF
  have hd : (Modulus p F.hp F.words).natDegree=F.words.length := by
    rw [F.exactMod,F.natDegree hf]
    exact hf.natDegree_map _
  exact (boxTransport_injective (ell:=ell) F.exactMod).comp (box_words_injective F.hp hm hd)

#print axioms bitWord_injective
#print axioms physical_scan
#print axioms box_words_injective
#print axioms frame_words_injective
end J6R32StatefulArithmetic
