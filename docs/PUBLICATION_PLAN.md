# Publication plan — JSP-001007 (before any push)

**GitHub account (plugin):** [@PskProduction](https://github.com/PskProduction) (Nikita)  
**Status:** plan only — **do not publish until you confirm this document.**

---

## What JSP actually requires (checked against CONTRIBUTING + attribution.md)

### Allowed claim role
| Role | You? |
|---|---|
| Mathematical solution | **No** — already Solved: Liam Price + GPT-5.4 Pro |
| Lean formalization | **Yes** — this is your claim |

### Hard rules
1. Proof lives in a **public** repo **owned by** `@PskProduction` (not a mirror of someone else’s proof).
2. Awards PR may edit **catalog only** — **no** `.lean` / lake files in `TheJustinSunPrize/awards`.
3. Catalog Lean row needs: repo URL, **branch**, **full 40-char SHA**, theorem names, build command, **Formalization contributors: @PskProduction**.
4. Claim issue later: same GitHub account = repo owner; contribution = **Lean formalization**.
5. **Ownership alone ≠ authorship.** Repo must explicitly credit `@PskProduction` as the Lean formalization author (`AUTHORSHIP.md` + commit author identity).
6. Complete proof: no `sorry`/`admit` in `Green44Asymp/` (already true). Standard axioms only.
7. Eligible ≠ payment (review → award record → KYC → private payment).

### What “видно что это я” must look like
- Repo under **your** account.
- `AUTHORSHIP.md` / README: **Lean formalization author: @PskProduction**.
- Git commits: `Author:` = your GitHub name/email (e.g. `PskProduction` / `117189263+PskProduction@users.noreply.github.com`).
- Catalog + claim: Formalization contributors: **@PskProduction** only (not Price; not “Cursor”).
- Honest note allowed: formalization produced in Cursor with AI assistance under your direction — still **your** claim as formalizer; math credit stays with Price.

---

## Recommended publish shape (clean for reviewers)

**New public repo** (preferred over dumping into a PNTAnd fork):

`https://github.com/PskProduction/jsp-001007-green44`

Contents:
```
README.md                 # build, theorems, math vs Lean credits
AUTHORSHIP.md             # you = Lean author; Price = math
LICENSE                   # MIT or Apache-2.0
lean-toolchain            # v4.32.2
lakefile.toml             # mathlib + PrimeNumberTheoremAnd (git pin)
lake-manifest.json        # after lake update (optional in first push)
Green44Asymp.lean
Green44Asymp/
  Statement.lean
  PrimeGaps.lean
  Cluster.lean
  Construction.lean
evidence/
  axioms-construction.log
  build-notes.md
```

Dependency: `PrimeNumberTheoremAnd` from  
`https://github.com/AlexKontorovich/PrimeNumberTheoremAnd`  
pinned to a known commit (local Mac path **must not** appear in public `lakefile.toml`).

**Import fix for standalone package:** change  
`PrimeNumberTheoremAnd.Green44Asymp.*` → `Green44Asymp.*`  
(keep `PrimeNumberTheoremAnd.Consequences` for `pi_alt`).

---

## Exact submission sequence

### A. Proof repository (you / agent after confirm)
1. Create `PskProduction/jsp-001007-green44` (public).
2. Push files with **your** commit identity.
3. Tag or note branch `main` + full SHA.
4. Verify: clone elsewhere / CI optional; at least document  
   `lake build Green44Asymp` (or package name we set).

### B. Catalog PR → `TheJustinSunPrize/awards`
1. Fork awards (or PR from branch).
2. Edit **only** `problems/catalog-1001-1022.md` `#JSP-001007`.
3. Set **Lean proof** → Yes + link + branch + SHA + `@PskProduction`.
4. Leave **Current status** Solved (Price / GPT-5.4 Pro).
5. Add **Attribution basis** if the template expects Lean attribution source → link `AUTHORSHIP.md` + repo.
6. PR description in English; no Lean sources attached.

### C. Claim (only after catalog shows Eligible / Unclaimed)
1. Issue: Claim an award.
2. Role: **Lean formalization**.
3. Repo URL: `https://github.com/PskProduction/jsp-001007-green44`.
4. Public contact email (will be public).
5. Do **not** claim mathematical solution.

---

## Risks / honesty (read once)

- Prize money is **not** guaranteed (empty historical bounty; no live award batches yet).
- Maintainers may ask how AI tools were used; disclosing Cursor assistance in `AUTHORSHIP.md` reduces dispute risk.
- Uploading only “someone else’s proof” is explicitly disallowed — your repo + your authorship file + your commits are the evidence chain.

---

## Confirm before I publish

Reply with something like:

> **ОК публиковать** как `PskProduction/jsp-001007-green44`

Optional:
- public email for later claim (or say “later”)
- license preference (default MIT)

Until then: **no create_repository / no push / no awards PR.**
