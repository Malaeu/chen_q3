# LINUX GATE — пять узлов после аудита Codex: GREEN

```yaml
DATE: 2026-08-21
REASON: >-
  Аудит Codex (CODEX_AUDIT_2026-08-21.md) нашёл, что у пяти файлов
  ОТСУТСТВОВАЛИ гейт-артефакты (его находка №4, traceability), и что два из них
  несли скрытый усиленный вход. Этот артефакт закрывает первое и фиксирует
  квитанции ПОСЛЕ починки второго.
WRITTEN_BY: Linux-тело
AUDITOR: Codex, независимо, все 30 механических команд EXIT 0

FILES_AND_RECEIPTS (после починки):
  G6N1EvenCenterDerivative.lean               blob 28682c3a  sha256 8db4ad36426fae72
  G6N1CenterNormalizedUniquenessReceiver.lean blob 7ec1470f  sha256 0e05199863e443f2
  G6N1Satz9SourcePackageInterface.lean        blob 7c3b781e  sha256 73b2280b8d38fa4e
  G6N1EvenSolutionCenterNonvanishing.lean     blob db7b2a7d  sha256 6e5e68449d7539e7
  G6N1OrderedEnumerationLock.lean             blob ce6c9d2e  sha256 eea83997163808e9

CHECKS: lake env lean, lake build, q3_check — все EXIT 0, "q3_check ok"
  профили: стандартная тройка; sorryAx НЕТ

ЧТО ПОЧИНЕНО ПО АУДИТУ:

  1. F72_0B2_GLOBAL_NORMALIZED_CONTINUITY_CONTRACT_GAP — НАСТОЯЩИЙ ДЕФЕКТ.
     Я требовал глобальную `Continuous (centerNormalized ·)`, тогда как REQ-K
     задавал `ContinuousOn ... (Icc ...)`, и полка даёт только его
     (`physicalComplex_continuousOn_closed`).
     ПОДТВЕРЖДЕНО ХУЖЕ, ЧЕМ ЗАЯВЛЕНО: production `normalizedPhysicalMode` есть
     `Icc.indicator` нуль-продолжение, на концах окна значение НЕнулевое
     (`D0Mode4FerrersEndpointFlux.lean:238`). Значит глобальная непрерывность
     не «сильнее», а ЛОЖНА для наших мод, и endpoint extension был доказан
     верно, но ПУСТ ровно там, где нужен. Ядро этого видеть не могло:
     импликация верна, недостижима посылка.
     ИСПРАВЛЕНО: приёмник и оба пакета переведены на `ContinuousOn` на `Icc`
     через `Set.EqOn.of_subset_closure`. Поле переименовано в
     `normalized_continuousOn`, чтобы старое имя не прошло молча.

  2. SATZ9_SOURCE_NONTRIVIALITY_TYPED_PORT_GAP — верно.
     Мой докстринг говорил, что `center_ne` следует из ОСТАЛЬНЫХ ПОЛЕЙ
     `Satz9SourceData`. Не следует: поля нетривиальности там нет, а нулевая
     функция удовлетворяет всем, какие есть. «Собственная функция» значит
     ненулевую на бумаге, но бумажный смысл не есть Lean-гипотеза.
     ИСПРАВЛЕНО: формулировка сужена, обязанность передана поставщику.

  3. Докстринг замка порядка заявлял отождествление ветвей.
     Не заявляет: теорема абстрактна и ПРЕДПОЛАГАЕТ равенство низов,
     поставка которого и есть W13.7B/W13.7E.
     ИСПРАВЛЕНО.

  4. Отсутствие гейт-артефактов — закрыто ЭТИМ файлом.

  5. Устаревшая квитанция a7407963 в протоколе и строке 12 — заменена.

ЧТО АУДИТ ПОДТВЕРДИЛ ЗЕЛЁНЫМ (не трогалось):
  пакет D, словарь параметров, сплетение операторов, цилиндры D0/D4,
  центральный якорь — 5/5 SEMANT PASS.
  Множитель sqrt(2*pi) верен; вероятностный Эрмит без лишней 2^(-n/2);
  разложение (1/16)D_4 - (3/16)D_0 подтверждено независимо по трём
  коэффициентам; скаляры не подогнаны.

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```
