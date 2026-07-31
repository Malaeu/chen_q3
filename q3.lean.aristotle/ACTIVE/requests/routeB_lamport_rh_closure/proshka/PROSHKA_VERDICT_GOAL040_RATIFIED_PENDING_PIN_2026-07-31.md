# PROSHKA VERDICT — GOAL_040_CORRECTIONS_RATIFIED_PENDING_PIN
Date received: 2026-07-31
Channel: owner-relayed chat (Proshka has no write access)
Materialized by: conductor-CLI (Claude Code, Linux) on owner's direct order
(Mythos had delegated to Codex; Filesystem bridge down in Mythos session)
Consumed by: docs/routeB_bus/041_goal040_postclose_requirements_audit.md;
proshka/RULE_NAMING_DISAMBIGUATION_2026-07-31.md
Transport artifacts note: payload is verbatim as pasted by the owner from the
Proshka browser chat; copy-paste escaping artifacts are preserved unmodified
(backslash-escaped underscores in headings, "## STATUS" heading level, fences
rendered as ```markdown). Semantic content untouched; no editing performed.

--- VERBATIM PAYLOAD BEGINS ---

## STATUS: CONDITIONAL — GOAL\_040\_CORRECTIONS\_RATIFIED\_PENDING\_PIN

```markdown
primary_verdict: GOAL_040_CORRECTIONS_RATIFIED
goal_040_source_status: USER_REPORTED_NOT_YET_PIN_VERIFIED
rule_0_status: PENDING_EXACT_TWO_TEXTS_COMPARISON

route_state: CHALLENGER_NOT_RH
bus_010: VOID
state_promotion: false
rh_claimed: false

t4a_supplier:
  status: SUPERSEDED_BY_039_LOCAL_PROOF
  submit: false
  duplicate_aristotle_run: forbidden

pl2_corrections:
  derivative_identification:
    verdict: RATIFIED
    failure_code: PL2_DERIV_IDENTIFICATION_API_GAP
  zero_mass_by_translation_invariance:
    verdict: RATIFIED
  strict_log_moment_by_separated_constant_bounds:
    verdict: RATIFIED

next_action:
  owner_conductor: mirror_sync_and_supply_pinned_goal_040_and_rule_0_texts
  judge: exact_text_ratification_only
  codex_or_aristotle: no_new_dispatch_from_this_verdict
```

## ROUTE MAP

Три поправки Mythos математически правильные.

### 1\. Деривативная идентификация — обязательна

PL2 должен получить не просто отрицательный логарифмический момент, а

$$
\operatorname{deriv}(\operatorname{Mellin}h)(1)\neq0.
$$

Между ними нужен отдельный exact bridge:

$$
\boxed{
\operatorname{deriv}(\operatorname{Mellin}h)(1)
=
\int_{0}^{\infty} h(u)\log u\,du.
}
$$

Это не definitional simplification: необходимы локальная интегрируемость, допустимость дифференцирования по комплексному параметру и точная Mellin-конвенция. Поэтому новый код

```markdown
PL2_DERIV_IDENTIFICATION_API_GAP
```

закрывает реальный source–target type gap, а не добавляет бюрократию. `[ABSTRACT][CONDITIONAL]`

### 2\. Нулевая масса через трансляционную инвариантность — лучший маршрут

Если

$$
h=\varphi-\tau_c\varphi,
\qquad
(\tau_c\varphi)(u)=\varphi(u-c),
$$

то при допустимой измеримой интегрируемой $\varphi$

$$
\int_{\mathbb R}\tau_c\varphi
=
\int_{\mathbb R}\varphi
$$

по трансляционной инвариантности меры Лебега, а значит

$$
\int h=0.
$$

Это сильнее и чище ручного вычисления двух треугольных интегралов: форма bump может впоследствии меняться, а доказательство массы останется тем же. Нужно только source-lock’нуть extension-by-zero и убедиться, что обе поддержки лежат в положительной полуоси, используемой Mellin transform. `[ABSTRACT][PAPER]`

### 3\. Строгость log-момента через константные границы — ратифицирована

Пусть две неотрицательные равномассные bump-функции имеют массу $m>0$, причём

$$
\operatorname{supp}\varphi\subset[a,b],
\qquad
\operatorname{supp}\psi\subset[c,d],
\qquad
0<a\le b<c\le d.
$$

Тогда

$$
\int\varphi(u)\log u\,du
\le
m\log b,
$$

а

$$
\int\psi(u)\log u\,du
\ge
m\log c.
$$

Следовательно,

$$
\int(\varphi-\psi)\log u\,du
\le
m(\log b-\log c)<0.
$$

Это даёт строгий знак без вычисления точного логарифмического интеграла. В Lean это также лучше: используются монотонность `Real.log`, неотрицательность, монотонность интеграла и точное равенство масс. `[ABSTRACT][PAPER]`

T4a действительно уже закрыт локально: Goal 039 фиксирует theorem `mellin_compactSupport_analyticOnNhd`, снятие `H_mellin` из T5 и отсутствие необходимости нового Aristotle iteration. Контракт v3 уже помечен `SUPERSEDED_BY_039_LOCAL_PROOF / DO_NOT_SUBMIT`; повторный запуск запрещён как дублирующий.

## FINAL PROPOSAL

Goal 040 принимать в repaired форме, где доказательная цепочка PL2 выглядит ровно так:

$$
\boxed{
\text{translated equal-mass bumps}
}
$$
 
$$
\Downarrow
$$
 
$$
\boxed{
\int h=0
}
$$
 
$$
\Downarrow
$$
 
$$
\boxed{
\int h(u)\log u\,du<0
}
$$
 
$$
\Downarrow\quad
\texttt{PL2\_DERIV\_IDENTIFICATION}
$$
 
$$
\boxed{
\operatorname{deriv}(\operatorname{Mellin}h)(1)\neq0
}
$$
 
$$
\Downarrow
$$
 
$$
\boxed{
\neg\operatorname{ContinuousAt}
\bigl(w\mapsto\zeta(w)\operatorname{Mellin}h(w)\bigr)\,1.
}
$$

`[ABSTRACT][CONDITIONAL]`

Ни одна стрелка не должна заменяться численным интегралом или утверждением «очевидно по дифференцированию под знаком интеграла».

### Registered prediction P040-PL2

```markdown
Generic simple-zero ⇒ raw-product discontinuity
закроется переиспользованием уже существующего residue/slope theorem.

Основное Lean-трение будет в exact derivative identification
deriv(Mellin h) 1 = ∫ h log,
а не в финальном доказательстве разрыва.
```

`[ABSTRACT][CONDITIONAL]`

## STRONGEST ATTACK

Сильнейшее возражение к repaired Goal 040:

> Отрицательный log-момент ещё не является отрицательной производной Mellin transform, пока не доказана законность дифференцирования и не сверена нормировка комплексной степени.

Именно поэтому новый failure code нужен. Без этого Codex мог бы доказать:

```markdown
∫ h(u) log u du < 0
```

и затем перескочить к

```markdown
deriv (Mellin h) 1 ≠ 0
```

через неподтверждённое тождество. Это было бы доказательством соседнего факта, а не PL2.

Второе возражение:

> Константные границы дают строгий знак только при положительной массе и строгом разделении поддержек.

Поэтому Goal 040 обязан иметь явные поля:

```markdown
bump_mass > 0
right_support_lower > left_support_upper
```

Удаление любого из них должно ломать strictness. Если поддержки только касаются, получается максимум $\le0$, не `<0`.

## CODEX DIRECTIVE

```markdown
NO_NEW_DIRECTIVE.

Goal 040 уже сформулирован диспетчером.
Не создавать конкурирующий PL2 goal.
Не отправлять T4a supplier в Aristotle.
Не пересобирать pole-subtracted shell.

После mirror-sync судья проверяет только:
  1. точный текст Goal 040;
  2. наличие трёх repaired slots;
  3. точные primary/failure codes;
  4. обе формулировки Rule 0.
```

## RULE 0 — КРИТЕРИЙ РАТИФИКАЦИИ

Одна live-формулировка уже видна:

> по умолчанию сообщение агенту показывается владельцу, а не отправляется; прямое отправление разрешено только после явного «отправь»; адресат и канал указываются однозначно.

Для ратификации двух формулировок они должны быть семантически эквивалентны следующим трём условиям:

```markdown
R0.1 DEFAULT_SHOW:
  подготовка текста не является разрешением на отправку.

R0.2 EXPLICIT_SEND_AUTHORITY:
  отправка разрешена только явной текущей командой владельца;
  старое общее "go" или факт готовности goal не считается разрешением.

R0.3 RECIPIENT_AND_CHANNEL_LOCK:
  перед действием однозначно названы адресат и канал:
  "Aristotle, CLI", "Codex, CLI", "Прошке, браузер", и т. п.
```

Если одна версия говорит «не отправлять без явного разрешения», а другая допускает автоматическую отправку по state-machine phase, это не редакционная разница, а конфликт. Точная ратификация удерживается до pin-URL обеих версий.

## META CLOSEOUT

**Что стало меньше?**  
PL2 разложен на три независимых и проверяемых кирпича: mass, log-moment, derivative identification.

**Что убито?**

- повторный T4a-run;
- ручное вычисление массы как обязательный путь;
- точное вычисление log-интеграла там, где достаточно разделения поддержек;
- неявный переход от log-момента к производной Mellin transform.

**Что нельзя повторять?**

Нельзя считать theorem

$$
\int h\log<0
$$

готовым PL2 без theorem

$$
\operatorname{deriv}(\operatorname{Mellin}h)(1)=\int h\log.
$$

**Current smallest named gap:**

```markdown
PL2_DERIV_IDENTIFICATION_API_GAP
```

**Следующий решающий тест:**

```markdown
lake-check exact derivative-identification lemma
under the actual Mellin definition and bump hypotheses.
```

**Rule 0:** математически не связан с PL2; его exact-text ratification остаётся отдельным control-plane актом после mirror-sync.

```markdown
iteration:
  target: Goal_040_PL2_repair
  status: OPEN
  failed_strategy: implicit_derivative_identification_and_duplicate_T4a_cloud_run
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: PL2_DERIV_IDENTIFICATION_API_GAP
  invariant_learned: strict log moment and Mellin derivative are distinct typed objects
  forbidden_future_move: send prepared text or duplicate theorem without explicit owner authorization
  next_decisive_test: pinned_goal_040_and_rule0_exact_text_audit
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

--- VERBATIM PAYLOAD ENDS ---
