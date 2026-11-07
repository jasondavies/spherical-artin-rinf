# Cold referee report, R∞ manuscript: summary

**Recommendation: minor revision.** The referee found no mathematical error, and all computations reproduced. They independently checked H3 and F4 with their own code, `own_check.py`.

## Required changes

1. **Remove the ATLAS from the E8 case.** The referee gives a proof that needs no computer:
   - [G,G] has index 2 and is characteristic.
   - The involutions outside [G,G] are the 120 reflections plus one class of 37800 elements, ±(products of 3 orthogonal reflections). This uses Carter's Lemma 5.
   - So the reflections form the unique outer involution class of size 120.
   - An automorphism preserving reflections is inner, by the tree diagram argument with sign choice; the result is an isometry of the E8 lattice, hence lies in W(E8).
   - Alternatively, cite Bannai and Franzsen–Howlett for Aut(W).
   - Also prove C_G(S) = 1.
   - Cite Steinberg for Out(Ω8+(2)) = S3.
   - The referee's `e8_involutions.py` gives a computational confirmation: the reflections are the unique involution class of size 120, and the class sizes and centralizer orders match.
2. **Disclose that Cohen–Paris Thm 1.4 is computer-assisted** (GAP, their §5, Cor 5.5) for exactly the types H4, F4, E6, E7, E8.
3. **Qualify the "two independent programs" claim** for Out(E7) and Out(E8).
4. **Fix three wording or justification errors:**
   - Prop 4.3 wording: in F4, only the short (resp. long) simple reflections act nontrivially on U_short (resp. U_long).
   - Table 1, F4 row: the "2·9" justification is invalid as written. Use the rank-3 actions plus orbital count instead.
   - Remark 5.2: delete or verify the FLT/Jabara sentence.
5. **Correct the claim about Calvez–Soroko:** for I2(m) they use virtual freeness of A/Z, not an explicit Aut.
6. **Add Dhanwani–Kumar–Naik–Singh**, arXiv:2409.10270.
7. **Weaken the hypothesis of Thm 3.1** to α induced from Aut(A).
8. **Fix notation clashes:** R vs R(φ), M vs M_φ, χ vs χ_U, and ρ.
9. **Housekeeping:**
   - add journal references for GGO17 and Marin;
   - state Prop 2.6 for all spherical A;
   - note that the README run `eig.py D5` crashes.
10. **Remove all [GAP] markers.** Keep the AI placeholder for the user.

## Optional, high value

Run the criterion uniformly for all irreducible spherical types. That would give a single proof of the whole classification that never needs Aut(A).
- **A_n** should be immediate once the hypothesis is weakened.
- **B_n, D_n, I2(m)** need either a proof or an explanation of where the criterion fails.

Files: `own_check.py`, `e8_involutions.py`, `f4_blocks.py`, `runs/`, `arxiv/`.
