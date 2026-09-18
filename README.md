# jsp-001007-green44

Lean 4 formalization of **Price’s Theorem 1** for **JSP-001007 / Green Problem 44**:
for all sufficiently large `N` there is a counterexample to the universal half-residue
bound, hence `¬ UniversalBound`.

## Credits

| Part | Credit |
|---|---|
| Mathematics | Liam Price and GPT-5.4 Pro (Solved in JSP catalog) |
| **Lean formalization** | **[@PskProduction](https://github.com/PskProduction)** |

See [AUTHORSHIP.md](AUTHORSHIP.md).

## Theorems

- `Green44Asymp.priceTheorem1`
- `Green44Asymp.not_universalBound`

## Build

Requires [elan](https://github.com/leanprover/elan) (Lean 4.32.2 per `lean-toolchain`).

```sh
export LEAN_NUM_THREADS=2   # optional on small machines
lake build Green44Asymp
```

First build downloads Mathlib and PrimeNumberTheoremAnd (large).

## Axioms

`#print axioms Green44Asymp.priceTheorem1` reports only:
`propext`, `Classical.choice`, `Quot.sound`
(see `evidence/axioms-construction.log`).

## JSP

Problem: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-1001-1022.md#JSP-001007  
This repo is the **Lean proof source** for a formalizer claim only.
