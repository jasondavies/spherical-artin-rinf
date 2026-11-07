# Note for an external reviewer (geometric group theory)

**Provenance.** This work is AI-assisted. The argument, code and manuscript were produced with an AI system (Claude).
They were checked by AI review only: an internal audit, plus one AI "cold referee" (recommendation: minor revision,
no mathematical errors, all computations reproduced). The present version addresses that report; see the table in
AUDIT.md. No human expert has checked it. We are asking you to be that check.

**Claim.** The Artin groups of spherical types E6, E7, E8, F4, H3 and H4 have property R∞. Combined with
Calvez–Soroko (A_n, B_n, D4, I2(m)) and Soroko–Vaskou (D_n, n ≥ 6; D5 as credited in Soroko arXiv:2610.13904), this
gives R∞ for every irreducible spherical Artin group of rank ≥ 2.

**Precise novelty.**
- New: the six exceptional types. Aut(A) is unknown for them, and the proof never uses it.
- Not new: A_n (proved here by hand, without Aut), B_n/D_n for n ≤ 7 including D5, and I2(9), I2(15), which are
  re-proved by the same criterion with exact computation. The uniform inversion result is also not new.
- Method precedent: Dekimpe–Gonçalves–Ocampo (eigenvalue 1 from reflection-group representations). The map f is
  equivalent to Cohen–Paris Lemma 3.7.

**Argument in five lines.**
1. P = ker(A→W) is characteristic (Cohen–Paris Thm 1.4). **Note:** for these types that proof uses GAP computations
   ([CP03] §5); we have not re-run them.
2. H₁(P;ℤ) ≅ ℤ^T as a permutation module, without signs, via f: A → ℤ^T ⋊ W, s ↦ (e_s, s).
3. φ acts on H₁(P) as πN, where π is a permutation realising the induced automorphism θ_φ of W/Z, and N commutes
   with W.
4. N = ±1 on a rational, absolutely irreducible, multiplicity-one constituent U (Schur plus lattice).
5. Twisting by an inner automorphism gives eigenvalue 1, hence R(φ|_P) = ∞ and R(φ) = ∞. F4 uses a swap variant.

**What to check (in order).**
1. Thm 3.1 and its proof, especially case (ii).
2. Prop 2.6.
3. Lemma 2.12 (certificates).
4. Lemma 3.5 and Prop 4.2: the computer-free proof that Out(W(E8)/±1) = 1. It uses the commutator subgroup,
   involution classes via Steinberg's theorem, and the sign-choice/isometry argument.
5. Prop 4.1: Out(W/Z) for E6, E7, H3, H4 and F4 is by computer. E7 rests on one enumeration plus cross-checks; see
   the qualification in the text.
6. §5: A_n by hand. Remark 5.3 states exactly what is missing for a uniform B_n/D_n proof (reflection preservation
   for all n). Remark 5.4 explains why the criterion cannot work for I2(m), m prime ≥ 5.

**Literature questions.**
- (a) Is R∞ for any of E6–E8, F4, H3, H4 known or announced?
- (b) Is H₁(P) = ℤ[T] (or A/[P,P]) used in the R∞ literature?
- (c) What is the correct attribution for D5?
- (d) Is there a reference showing that automorphisms of W/Z(W) induced from Aut(A) preserve reflections for all
  B_n and D_n? Franzsen–Howlett–Mühlherr may be relevant. This would complete a uniform, Aut-free proof of the
  classification, apart from I2(m).
- (e) Exact section numbers for the standard facts cited from Humphreys and Orlik–Terao.

**Reproduce** (Python 3 + numpy + sympy; about 4 minutes in total; see `code/README.md`):
```
cd code && python3 certify.py H3 F4 H4 E6 E7 E8 D5 && python3 certify_outer.py H3 F4 H4 && python3 check.py
cd indep && python3 indep_check.py H3 F4 H4 E6 E7 && python3 indep_check.py commutant:E8
python3 out_check.py H3 F4 H4 D5 E6 E7 && python3 out_check_stab.py E7 E8
python3 uniform_check.py A5 B5 D4 D5 D6 "I2(5)" "I2(9)" && python3 referee_e8_involutions.py && python3 referee_own_check.py H3 F4
```
