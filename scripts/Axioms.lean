import CompanionMatrix

/-! Axiom audit. Every proved result must depend only on `propext`, `Classical.choice` and
`Quot.sound`. `scripts/check_axioms.sh` fails if anything else (e.g. `sorryAx`) appears. -/

-- Lemma A
#print axioms CompanionMatrix.phi_eq
#print axioms CompanionMatrix.phi_nonneg
#print axioms CompanionMatrix.phi_le_one
#print axioms CompanionMatrix.phi_mem_Icc
#print axioms CompanionMatrix.phi_vecMulVec
#print axioms CompanionMatrix.phi_vecMulVec'
#print axioms CompanionMatrix.psi_vecMulVec
#print axioms CompanionMatrix.phi_normalize
-- Lemma B
#print axioms CompanionMatrix.lemmaB
#print axioms CompanionMatrix.lemmaB_cos
#print axioms CompanionMatrix.lemmaB_left
-- Theorem 2 (strict dominance)
#print axioms CompanionMatrix.tendsto_of_rankOne_approx
#print axioms CompanionMatrix.theorem2
#print axioms CompanionMatrix.inner_coordVec_of_ne
-- Theorem 1 (order 2)
#print axioms CompanionMatrix.transport_mulVec
#print axioms CompanionMatrix.theorem1
#print axioms CompanionMatrix.transport_eq_vecMulVec
#print axioms CompanionMatrix.tendsto_psi_transport
#print axioms CompanionMatrix.theorem1_phi
#print axioms CompanionMatrix.theorem1_phi_infty
