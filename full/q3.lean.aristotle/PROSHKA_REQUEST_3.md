# PROSHKA REQUEST v3: Сверка с базой (BASE-SYNCED)

---

## §0. Статус и цель

**Цель:** Доказать только $Q(\Phi) \geq 0$ для всех $\Phi \in \mathcal{W}$.

**Статус:** Условная схема «Tier-2 ⟹ RH» через Weil criterion (никаких "RH proven").

---

## §1. Нормировка / знак / тор (ФИКСИРУЕМ)

### Знак (МИНУС!)
$$
Q(\Phi) = Q_{\mathrm{arch}}(\Phi) - Q_{\mathrm{prime}}(\Phi)
$$

### T0-нормировка
$$
a_*(\xi) = 2\pi a(\xi), \qquad \xi_n = \frac{\log n}{2\pi}
$$

### Period-1 тор
$$
\mathbb{T} = [-1/2, 1/2], \quad e_k(\theta) = e^{2\pi i k\theta}, \quad d\theta
$$

### Символ A3 (period-1)
$$
P_A(\theta) = 2\pi \sum_{m \in \mathbb{Z}} g_{B,t_{\mathrm{sym}}}(\theta + m), \quad g_{B,t}(\xi) = a(\xi)\Phi_{B,t}(\xi)
$$

---

## §2. Tier-1 факты

### Weil criterion
$$
Q \geq 0 \text{ на } \mathcal{W} \iff \mathrm{RH}
$$

### Szegő-Böttcher (period-1)
$$
\lambda_{\min}(T_M[\sigma]) \geq \min\sigma - C_{SB} \cdot \omega_\sigma\left(\frac{1}{2M}\right), \quad C_{SB} = 4
$$

---

## §3. Tier-2 модули (по базе)

### A1': Плотность Fejér×heat-конуса
При фиксированном $t_{\mathrm{sym}}$.

### A2: Lipschitz-контроль
$Q$ липшицев на каждом $\mathcal{W}_K$.

### A3 floor (pointwise)
$$
P_A(\theta) \geq c_* = \frac{11}{10} \quad \forall\theta \in [-1/2, 1/2]
$$

### RKHS-cap
При $t_{\mathrm{rkhs}} \geq t_{\star,\mathrm{rkhs}}^{\mathrm{unif}} = 1$:
$$
\|T_P\| \leq \rho(1) < \frac{1}{25}
$$

### Rayleigh-мост
$Q(\Phi_{B,t_{\mathrm{sym}}})$ равен Rayleigh-квотенту $T_M[P_A] - T_P$ при $p \equiv 1$, без внешнего $2\pi$ (он уже в $P_A$).

---

## §4. Дискретизация

$$
\lambda_{\min}(T_M[P_A]) \geq \min P_A - C_{SB} \cdot \omega_{P_A}\left(\frac{1}{2M}\right)
$$

$$
M_0^{\mathrm{unif}} = \left\lceil \frac{C_{SB} L_*}{c_*} \right\rceil, \quad
M \geq M_0^{\mathrm{unif}} \Rightarrow \lambda_{\min}(T_M[P_A]) \geq \frac{c_*}{2}
$$

---

## §5. Позитивность на генераторах

1. **A3:** $\min P_A \geq c_*$
2. **Discretisation:** $\lambda_{\min}(T_M[P_A]) \geq c_*/2$
3. **RKHS-cap:** $\|T_P\| \leq c_*/4$ (через $\rho(1) < 1/25$)

Отсюда:
$$
\lambda_{\min}(T_M[P_A] - T_P) \geq \frac{c_*}{4} > 0
$$

и $Q(\Phi_{B,t_{\mathrm{sym}}}) \geq 0$.

---

## §6. Замыкание и RH

По A1'+A2 переносим $Q \geq 0$ с генераторов на всё $\mathcal{W}_K$, затем на $\mathcal{W}$.

По Weil criterion получаем **RH (условно на Tier-2)**.

---

## §7. Ключевые инварианты (проверка)

| # | Инвариант | Значение |
|---|-----------|----------|
| 1 | Знак | $Q = Q_{\mathrm{arch}} - Q_{\mathrm{prime}}$ |
| 2 | Нормировка | $\xi_n = \log n/(2\pi)$, $a_* = 2\pi a$ |
| 3 | Тор | period-1, $\mathbb{T} = [-1/2, 1/2]$ |
| 4 | Символ | $P_A = 2\pi \sum_m g(\theta+m)$ |
| 5 | Floor | $c_* = 11/10$ (НЕ 1.5!) |
| 6 | Toeplitz-gap | $\omega(1/(2M))$, $M_0 = \lceil C_{SB}L_*/c_* \rceil$ |
| 7 | Prime-cap | $t_{\mathrm{rkhs}} \geq 1 \Rightarrow \rho(1) < 1/25$ |
| 8 | Цель | $Q(\Phi) \geq 0$ (НЕ "≥ 1.125"!) |

---

## §8. Формат ответа

- Короткий отчёт "совпадает/не совпадает" по пунктам 1-8
- Пересобранный текст §0-§8 (одним блоком)
- Без внешних ссылок; без новых обозначений; без legacy-веток

---

## ЧЕГО НЕ ДЕЛАТЬ

❌ Не возвращать $c_* = 1.5$
❌ Не писать SB как $O(1/M)$; только $C_{SB} \cdot \omega(1/(2M))$
❌ Не ставить $t_{\mathrm{rkhs}} = t_{\mathrm{sym}}$
❌ Не вводить $2\pi$-периодизацию
❌ Не писать $Q \geq 1.125$ без нормировки

---

## Контекст-пакет (.tex база)

| Файл | Модуль |
|------|--------|
| `full/sections/T0.tex` | T0 нормировка |
| `full/sections/A3/symbol_floor.tex` | A3 floor |
| `full/sections/A3/rayleigh_bridge.tex` | Rayleigh мост |
| `full/sections/A3/matrix_guard.tex` | Дискретизация |
| `full/sections/RKHS/prime_trace_closed_form.tex` | RKHS cap |
| `full/sections/A1prime.tex` | A1' density |
| `full/sections/A2.tex` | A2 Lipschitz |
| `full/sections/Main_closure.tex` | Замыкание |
| `full/sections/Weil_linkage.tex` | Weil linkage |

---

**∎ END OF PROSHKA REQUEST v3**
