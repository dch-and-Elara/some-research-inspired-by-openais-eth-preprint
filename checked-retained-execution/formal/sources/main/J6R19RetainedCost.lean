import J6R19RetainedPromote

/-! The complete parse/resize/emit cost is linear in the stored and
emitted rectangular bit lengths, plus the two header lengths. -/
namespace J6R19Retained

theorem promoteFee_closed_form (e ell p q oldWidth newWidth : ℕ) :
    promoteFee e ell p q oldWidth newWidth =
      6*oldWidth+4*newWidth+ell*(e*(10*p+12*q+16)+16)+29 := by
  unfold promoteFee ingressFee cutUVFee cutUFee cutWordFee boxFee scalarFee wordFee
  ring

#print axioms promoteFee_closed_form
end J6R19Retained

