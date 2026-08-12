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

def dumpOne (env : Environment) (n : Name) (ci : ConstantInfo) : MetaM (Option String) := do
  if isNoise n then return none
  let typeStr ← try (toString <$> ppExpr ci.type) catch _ => pure "<pp failed>"
  let doc := (← findDocString? env n).getD ""
  -- `findDeclarationRanges?` даёт строку, но не файл. Имя файла берём из индекса
  -- модуля: это единственное место, где Lean хранит связь константы с модулем.
  let file :=
    match env.getModuleIdxFor? n with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none     => ""
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

/-- Печатать только объявления, чьё имя начинается с одного из префиксов.
    Пустой список префиксов означает «всё», чего для Mathlib делать не стоит. -/
def dumpEnv (prefixes : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut n := 0
  for (nm, ci) in env.constants.toList do
    -- только НАШИ модули: константы Mathlib сюда попадать не должны
    if env.getModuleIdxFor? nm |>.isSome then
      if prefixes.isEmpty || prefixes.any (·.isPrefixOf nm) then
        match ← dumpOne env nm ci with
        | some line => IO.println line; n := n + 1
        | none => pure ()
  IO.eprintln s!"-- объявлений напечатано: {n}"

end Q3EnvDump

open Q3EnvDump in
run_cmd Elab.Command.liftTermElabM do
  dumpEnv [`Q3]
