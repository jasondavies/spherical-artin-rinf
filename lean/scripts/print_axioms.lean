-- Run with: lake env lean scripts/print_axioms.lean   (after lake build)
import ArtinRinf
#print axioms ArtinRinf.reidemeister_quotient_le
#print axioms ArtinRinf.reidemeister_inner_comp
#print axioms ArtinRinf.reidemeister_restrict_le
#print axioms ArtinRinf.reidemeister_matEnd_eq_top
#print axioms ArtinRinf.eigenvalue_eq_one_or_neg_one
#print axioms ArtinRinf.reidemeister_eq_top_of_witness
#print axioms ArtinRinf.rinf_of_outGeneratedBy
#print axioms ArtinRinf.ReflData.rinf
#print axioms ArtinRinf.H3.artin_H3_R_infty
#print axioms ArtinRinf.H3.artin_H3_R_infty'
#print axioms ArtinRinf.F4.artin_F4_R_infty
#print axioms ArtinRinf.F4.artin_F4_R_infty'
#print axioms ArtinRinf.H4.artin_H4_R_infty
#print axioms ArtinRinf.E6.artin_E6_R_infty
#print axioms ArtinRinf.E7.artin_E7_R_infty
#print axioms ArtinRinf.E8.artin_E8_R_infty
#print axioms ArtinRinf.H3.artin_H3_R_infty_FH
#print axioms ArtinRinf.F4.artin_F4_R_infty_FH
#print axioms ArtinRinf.H4.artin_H4_R_infty_FH
#print axioms ArtinRinf.E6.artin_E6_R_infty_FH
#print axioms ArtinRinf.E7.artin_E7_R_infty_FH
#print axioms ArtinRinf.E8.artin_E8_R_infty_FH
#print axioms ArtinRinf.D5.artin_D5_R_infty
#print axioms ArtinRinf.D5.artin_D5_R_infty_FH
#print axioms ArtinRinf.ReflData.rinf_FH
#print axioms ArtinRinf.ReflData.TreeCert.conj
#check @ArtinRinf.H3.artin_H3_R_infty'
#check @ArtinRinf.F4.artin_F4_R_infty'
#check @ArtinRinf.E8.artin_E8_R_infty
#check @ArtinRinf.E8.artin_E8_R_infty_FH
#print ArtinRinf.FranzsenHowlett
#check @ArtinRinf.D5.artin_D5_R_infty_FH
#print ArtinRinf.D₅

#print axioms ArtinRinf.exists_fixed_of_lattice_sign_witness
#print axioms ArtinRinf.reidemeister_eq_top_of_lattice_matrix
#print axioms ArtinRinf.TwistedClassification.reidemeister_eq
#print axioms ArtinRinf.Dihedral5.reidemeister_phi
#print axioms ArtinRinf.Dihedral5.generated_eq_top
#print axioms ArtinRinf.Dihedral5.braid_relation
#print axioms ArtinRinf.Dihedral5.exists_reidemeister_eighteen
#print axioms ArtinRinf.Dihedral5.affineMap_injective
