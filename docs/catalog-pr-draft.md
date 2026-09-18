# Draft catalog edit for JSP-001007

Target file in PR against `TheJustinSunPrize/awards`:
`problems/catalog-1001-1022.md` (anchor `#JSP-001007`).

Replace the **Lean proof** row (currently `No`) with something like:

```text
| Lean proof | Yes — [Lean source](https://github.com/YOUR_USER/YOUR_REPO/blob/BRANCH/PrimeNumberTheoremAnd/Green44Asymp/Construction.lean)<br>Branch: `BRANCH`<br>Commit: `FULL_40_CHAR_SHA`<br>Theorems: `Green44Asymp.priceTheorem1`, `Green44Asymp.not_universalBound`<br>Build: `lake build PrimeNumberTheoremAnd.Green44Asymp.Construction`<br>Formalization contributors: @YOUR_USER. |
```

Leave **Current status** as Solved with Price / GPT-5.4 Pro unless maintainers ask otherwise.

Do **not** claim mathematical solver credit in this PR.

PR body checklist (awards CONTRIBUTING):

- Problem: JSP-001007 / Green 44
- Role: Lean formalization only
- Repo URL / branch / full SHA
- Statement matches Price Theorem 1 → ¬ UniversalBound (formal-conjectures Green 44 form)
- No `sorry` / `admit` in `Green44Asymp/`
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`
