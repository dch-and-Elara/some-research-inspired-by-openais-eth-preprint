import J6R24MeteredRecursionCentre

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000

/-! Prices the actual resident arithmetic without a hypothetical read cache:
every Lagrange basis rereads the complete probe roster, the inner strip
is charged even on failure, and each selected jet word is scanned. -/
namespace J6R48BitCost
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R22Active J6R23ScheduleWeight J6R24MeteredRecursion J6R9Recursive

theorem needsAt_all {p ell n : ℕ} {fw : List (Word p)}
    (load : Fin n → Meter (UVBlock fw ell)) (i : Fin n) :
    needsAt load i = bill load (probeOrder n) := by
  have pm := List.perm_cons_erase (probeOrder_mem i)
  have hm := (pm.map (fun j => (load j).steps)).sum_eq
  exact hm.symm

theorem site_probe_reload_exact {p ell k n : ℕ} {M : Type*}
    (I : SiteTape p ell k n M) :
    I.nodeBill = n * bill I.nodeM (probeOrder n) := by
  unfold SiteTape.nodeBill
  have same : (probeOrder n).map (needsAt I.nodeM) =
      (probeOrder n).map (fun _ => bill I.nodeM (probeOrder n)) :=
    List.map_congr_left (fun z _ => needsAt_all I.nodeM z)
  rw [same]
  have const (xs : List (Fin n)) :
      (xs.map (fun _ => bill I.nodeM (probeOrder n))).sum =
        xs.length * bill I.nodeM (probeOrder n) := by
    induction xs with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.add_mul,Nat.one_mul]
      omega
  exact (const (probeOrder n)).trans (by rw [probeOrder,List.length_ofFn])

def stripFee (e ell p B : ℕ) : ℕ :=
  6 + ell * (10 + e * (8 * (p+B+1) + p + 8) + e*p)

theorem strip_loop_measured {p B ell : ℕ} {old : List (Word (p+B))} {new : List (Word p)}
    (eq : old.length=new.length) (v : UVBlock old ell) :
    (stripUVLoop eq v).steps ≤ stripFee old.length ell p B := by
  have cap := checkedMap_steps (stripULoop eq) (new.length*p)
      (6+old.length*(8*(p+B+1)+p+8)) v.val (fun x _ => stripULoop_steps eq x)
  rw [v.property,←eq] at cap
  change (checkedMap (stripULoop eq) (new.length*p) v.val).steps+4 ≤ _
  have hV : (checkedMap (stripULoop eq) (new.length*p) v.val).steps ≤
      2+ell*(6+old.length*(8*(p+B+1)+p+8)+old.length*p+4) := by
    rw [←eq]
    exact cap
  unfold stripFee
  calc
    _ ≤ (2+ell*(6+old.length*(8*(p+B+1)+p+8)+old.length*p+4))+4 :=
      Nat.add_le_add_right hV 4
    _ = _ := by ring

theorem weighted_term_measured {f : ℤ[X]} {p q ell k a M u B j : ℕ} {t : ℤ}
    (low : Frame f p) (high : Frame f q) (hv : 0<ell) (hf : f.Monic)
    (ht : t∈J6ActiveSchedule.active a M u)
    (hB : HermiteLoss.totalLoss a (HermiteLoss.sourceH M u) j t≤B)
    (L : Roster a M u t) (jet : JetTape low.words ell k) (hj : j<k) :
    let h := (low.natDegree hf).trans (high.natDegree hf).symm
    (termM low.hp low.sizePos high.hp high.sizePos hv h jet a B j t L.rows).steps ≤
      termFee f.natDegree ell p q a B k j high.hp t L.rows := by
  let v := jetMap (J6R22Active.boxTransport (ell:=ell) low.exactMod) k (jetRead low.hp low.sizePos jet)
  obtain ⟨F,hF⟩ := AdjoinRoot.mk_surjective v
  exact (termM_exact low.hp low.sizePos high.hp high.sizePos hv hf low.exactMod high.exactMod
    ht hB L jet hj F hF.symm).2

#print axioms needsAt_all
#print axioms site_probe_reload_exact
#print axioms strip_loop_measured
#print axioms weighted_term_measured
end J6R48BitCost

