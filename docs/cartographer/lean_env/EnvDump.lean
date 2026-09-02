/-
  Lean environment dumper — слой 1 конструктора.

  ЗАЧЕМ. `atom_describe.py` читает исходный ТЕКСТ до `:=` или `by`. Человеку этого
  хватает, конструктору — нет. Текстовая сигнатура не содержит переменных из внешней
  `section`, неявных параметров, universe-параметров, посылок typeclass после
  elaboration, вставленных приведений и раскрытых нотаций. Решать по ней о
  применимости теоремы нельзя.

  Источником истины должен быть Lean environment. Этот файл его и печатает.
  `rg` остаётся быстрым передним краем, но не судьёй.

  ЧТО ПЕЧАТАЕТ. По одной JSON-записи на строку (JSON Lines), поля:

      name              полное имя с namespace
      kind              theorem / def / axiom / opaque / ctor / …
      type              ELABORATED тип, а не текст исходника
      levelParams       universe-параметры
      numBinders        число связывателей в теле типа
      file, line        позиция объявления, когда Lean её знает
      doc               докстринг
      typeConsts        константы, встречающиеся В ТИПЕ
      axioms            аксиоматическое замыкание доказательства
      isPrivate         приватность
      isUnsafe          небезопасность

  ЧЕГО НЕ ДЕЛАЕТ. Не судит применимость. Не сравнивает утверждения. Не ищет
  кандидатов. Это индекс, а не comparator.

  ЗАПУСК. Модули для импорта подставляются генератором `envdump.py`; сам файл
  запускается `lake env lean`.
-/
import Lean
-- IMPORTS_PLACEHOLDER

open Lean Meta Elab

namespace Q3EnvDump

/-- Экранировать строку для JSON. -/
def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | c    => if c.toNat < 0x20 then "" else c.toString

def jstr (s : String) : String := "\"" ++ jsonEscape s ++ "\""

def jarr (xs : Array String) : String :=
  "[" ++ String.intercalate "," (xs.toList.map jstr) ++ "]"

/-- Род объявления одним словом. -/
def kindOf : ConstantInfo → String
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "def"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "ctor"
  | .recInfo    _ => "rec"

/-- Сколько `∀`-связывателей на верхнем уровне типа. Грубая мера размера телескопа. -/
partial def countBinders (e : Expr) : Nat :=
  match e with
  | .forallE _ _ b _ => 1 + countBinders b
  | _ => 0

/-- Константы, встречающиеся в ТИПЕ. Это не атомы доказательства: тип несёт смысл
    утверждения, тело доказательства — только провенанс и цену. Смешивать их нельзя. -/
def constsInType (e : Expr) : Array Name :=
  (e.getUsedConstants).filter fun n => !n.isInternal

/-- Пропускать шум: внутренние имена, автогенерируемые леммы уравнений и прочее. -/
def isNoise (n : Name) : Bool :=
  n.isInternal
  || n.isImplementationDetail
  || (`_example).isPrefixOf n
  -- `|>.length > 1` без скобок парсится как аргумент `||`; ловится компилятором сразу
  || ((n.toString.splitOn "._").length > 1)

def dumpOne (env : Environment) (moduleName n : Name) (ci : ConstantInfo) : MetaM (Option String) := do
  if isNoise n then return none
  let typeStr ← try
    withOptions (·
        |>.setBool `pp.proofs true
        |>.setBool `pp.deepTerms true
        |>.setNat `pp.maxSteps 1000000) do
      toString <$> ppExpr ci.type
    catch _ => pure "<pp failed>"
  let doc := (← findDocString? env n).getD ""
  -- `findDeclarationRanges?` даёт строку, но не файл. Имя файла берём из индекса
  -- модуля: это единственное место, где Lean хранит связь константы с модулем.
  let file := moduleName.toString
  let line ←
    match ← findDeclarationRanges? n with
    | some r => pure (toString r.range.pos.line)
    | none   => pure ""
  -- аксиоматическое замыкание: единственный честный ответ на «доказано ли и на чём»
  let axs ← try (collectAxioms n) catch _ => pure #[]
  let fields : List String :=
    [ "\"name\":"        ++ jstr n.toString
    , "\"kind\":"        ++ jstr (kindOf ci)
    , "\"type\":"        ++ jstr typeStr
    , "\"levelParams\":" ++ jarr (ci.levelParams.map Name.toString).toArray
    , "\"numBinders\":"  ++ toString (countBinders ci.type)
    , "\"file\":"        ++ jstr file
    , "\"line\":"        ++ jstr line
    , "\"doc\":"         ++ jstr doc
    , "\"typeConsts\":"  ++ jarr ((constsInType ci.type).map Name.toString)
    , "\"axioms\":"      ++ jarr (axs.map Name.toString)
    , "\"isPrivate\":"   ++ (if isPrivateName n then "true" else "false")
    , "\"isUnsafe\":"    ++ (if ci.isUnsafe then "true" else "false")
    ]
  return some ("{" ++ String.intercalate "," fields ++ "}")

/-- Exact-name mode is proportional to the request, not the complete environment. -/
def dumpExact (env : Environment) (exactNames : List Name) : MetaM (List Name) := do
  let mut seen : List Name := []
  for nm in exactNames do
    match env.find? nm, env.getModuleIdxFor? nm with
    | some ci, some idx =>
        let moduleName := env.header.moduleNames[idx.toNat]!
        match ← dumpOne env moduleName nm ci with
        | some line => IO.println line; seen := nm :: seen
        | none => pure ()
    | _, _ => pure ()
  return seen

/-- Generic namespace/full mode retains the streaming environment scan. -/
def dumpStreaming (env : Environment) (prefixes modules : List Name) : MetaM Nat := do
  let mut n := 0
  -- Iterate the persistent environment map directly.  Converting the complete
  -- Mathlib environment to a list first duplicates millions of entries before
  -- the Route-B module filter can reject them, causing multi-gigabyte spikes.
  for (nm, ci) in env.constants do
    -- только НАШИ модули: константы Mathlib сюда попадать не должны
    match env.getModuleIdxFor? nm with
    | some idx =>
        let moduleName := env.header.moduleNames[idx.toNat]!
        if (modules.isEmpty || modules.contains moduleName) &&
            (prefixes.isEmpty || prefixes.any (·.isPrefixOf nm)) then
          match ← dumpOne env moduleName nm ci with
          | some line => IO.println line; n := n + 1
          | none => pure ()
    | none => pure ()
  return n

/-- Печатать только объявления выбранных модулей и пространств имён. Список
    модулей задаёт генератор по текущим `.lean` + `.olean`; транзитивно загруженная
    сирота или устаревший модуль не должен просочиться в индекс. -/
def dumpEnv (prefixes exactNames modules : List Name) : MetaM Unit := do
  let env ← getEnv
  let n ← if exactNames.isEmpty then
      dumpStreaming env prefixes modules
    else do
      let seenExact ← dumpExact env exactNames
      let missingExact := exactNames.filter fun nm => !seenExact.contains nm
      if !missingExact.isEmpty then
        let missingText := String.intercalate ", " (missingExact.map Name.toString)
        throwError m!"requested exact names missing: {missingText}"
      pure seenExact.length
  IO.eprintln s!"-- объявлений напечатано: {n}"

end Q3EnvDump

open Q3EnvDump in
run_cmd Elab.Command.liftTermElabM do
  dumpEnv [] [] []
