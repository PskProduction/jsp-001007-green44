# JSP-001007 — подготовка к подаче

## Короткий ответ

| Вопрос | Ответ |
|---|---|
| Lean-математика готова? | **Да** (`priceTheorem1`, `not_universalBound`) |
| Можно сразу жать Claim и ждать деньги? | **Нет** — сначала публичный репозиторий **ваш** + PR в каталог `Lean proof: Yes` |
| Нужен «коннектор» биржи / MetaMask? | **Нет** |
| Что нужно подключить | **GitHub-аккаунт**, которым вы владеете; репозиторий доказательства должен быть **owned by that account** |

Вы formalizer (Price уже Solved). Claim только на **Lean formalization**, не на mathematical solution.

---

## Порядок действий (как требует JSP)

### 1. Опубликовать proof-репозиторий (вы)

В awards **нельзя** коммитить Lean-исходники. Нужна ссылка на **ваш** public GitHub repo.

Рекомендуемый путь (легче всего):

1. На GitHub: Fork [`AlexKontorovich/PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).
2. Склонировать **свой** fork.
3. Скопировать папку  
   `PrimeNumberTheoremAnd/Green44Asymp/`  
   из рабочей копии на Mac  
   (`/Users/nikita/PycharmProjects/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/Green44Asymp/`).
4. Commit + push в **свой** fork (ветка, например `jsp-001007-green44`).
5. Записать **полный 40-символьный** commit SHA.

Альтернатива: отдельный repo (шаблон в этом каталоге `lakefile.toml`) с зависимостью на PNTAnd по git — но reviewers всё равно тянут Mathlib+PNTAnd; fork обычно проще.

### 2. PR в TheJustinSunPrize/awards (не исходники)

Только правка каталога:  
`problems/catalog-1001-1022.md` → секция `#JSP-001007`

Обновить поля примерно так:

- **Lean proof** → `Yes` + ссылка на файл/теорему + branch + **полный SHA** + Formalization contributors: `@ваш_github`
- Maintainers сами выставят Eligible / Claim status после ревью

Черновик текста: [`docs/catalog-pr-draft.md`](docs/catalog-pr-draft.md).

**Не** класть `.lean` / `lake-packages` в PR awards.

### 3. Claim (только после Eligible = Yes)

Issue form: [Claim an award](https://github.com/TheJustinSunPrize/awards/issues/new?template=claim-award.yml)

- Problem link → `#JSP-001007`
- Lean repository → URL **вашего** repo (owner = автор issue)
- Contribution → **Lean formalization**
- Mathematical solution **не** заявлять (авторы Price / GPT-5.4 Pro)

Eligible ≠ выплата (ревью, award record, KYC, private payment channel).

---

## Что уже доказано (для описания)

| Теорема | Файл |
|---|---|
| `many_primes_in_doubling` | `PrimeGaps.lean` |
| `clustered_thousand_primes` | `Cluster.lean` |
| `priceTheorem1` | `Construction.lean` |
| `not_universalBound` | `Construction.lean` |

Сборка (в дереве PNTAnd):

```sh
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=2
cd /Users/nikita/PycharmProjects/PrimeNumberTheoremAnd
lake build PrimeNumberTheoremAnd.Green44Asymp.Construction
```

Аксиомы (стандартные): `propext`, `Classical.choice`, `Quot.sound`  
(см. `evidence/axioms-construction.log`).

---

## Чеклист перед отправкой

- [ ] Public GitHub repo, **owner = ваш аккаунт**
- [ ] Ветка + полный commit SHA
- [ ] В README репозитория: как собрать, какие теоремы, роль formalizer
- [ ] PR в awards только с правкой каталога (+ attribution)
- [ ] После merge / Lean Yes → claim issue (Lean only)
- [ ] Не обещать себе выплату до confirmed award + KYC
