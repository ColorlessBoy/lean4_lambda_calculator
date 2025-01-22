import Lean
import Lean.Meta
import Std.Data.HashMap

open Lean Meta Tactic
open Lean System Meta

def parseName (str : String) : Name :=
  let parts := str.splitOn "."
  parts.foldl (fun acc part =>
    if part.startsWith "«" && part.endsWith "»" then
      -- 去掉两边的 "«" 和 "»"
      let cleanPart := part.dropRight 1 |>.drop 1
      Name.mkStr acc cleanPart
    else if part.toNat?.isSome then
      -- 优先处理纯数字的部分
      Name.mkNum acc part.toNat!
    else
      -- 普通字符串标识符
      Name.mkStr acc part
  ) Name.anonymous

def _getDeps (expr : Expr) (context : List String) : MetaM (List String) := do
  match expr with
  | Expr.const name _ =>
    let nameStr := s!"{name}"
    if nameStr ∈ context then
      pure context
    else
      pure (context ++ [nameStr])
  | Expr.app f arg =>
    let mut context ← _getDeps f context
    context ← _getDeps arg context
    pure context
  | Expr.lam _ ty body _ | Expr.forallE _ ty body _ | Expr.letE _ _ ty body _ =>
    let mut context ← _getDeps ty context
    context ← _getDeps body context
    pure context
  | _ => pure context

def _hasProj (body : Expr) : Bool :=
  match body with
  | Expr.app f arg => _hasProj f || _hasProj arg
  | Expr.lam _ ty body _ | Expr.forallE _ ty body _ =>
    _hasProj ty || _hasProj body
  | Expr.letE _ _ value body _ =>
    _hasProj value || _hasProj body
  | Expr.mdata _ value => _hasProj value
  | Expr.proj _ _ _ => true
  | _ => false

def getDeps (name : Name) : MetaM (String × (List String)) := do
  let env ← getEnv
  match env.find? name with
  | some (ConstantInfo.axiomInfo ax) =>
    -- 公理：只有类型，没有值
    let deps ← _getDeps ax.type []
    pure ("axiom", deps)
  | some (ConstantInfo.thmInfo thm) =>
    -- 定理：有类型和证明值
    let context ← _getDeps thm.type []
    let deps ← _getDeps thm.value context
    if _hasProj thm.value then
      pure ("axiom", deps)
    else
      pure ("theorem", deps)
  | some (ConstantInfo.defnInfo defn) =>
    -- 定义：有类型和定义体
    -- 定理：有类型和证明值
    let context ← _getDeps defn.type []
    let deps ← _getDeps defn.value context
    if _hasProj defn.value then
      pure ("axiom", deps)
    else
      pure ("def", deps)
  | some (ConstantInfo.ctorInfo ctor) =>
    -- 构造函数：有类型，但无单独定义值
    let deps ← _getDeps ctor.type []
    pure ("axiom", deps)
  | some (ConstantInfo.recInfo rec) =>
    -- 消去规则（recursor）：有类型，但无定义值
    let deps ← _getDeps rec.type []
    pure ("axiom", deps)
  | some (ConstantInfo.inductInfo ind) =>
    -- 归纳定义：有类型，但无定义值
    let deps ← _getDeps ind.type []
    pure ("axiom", deps)
  | some (ConstantInfo.quotInfo val) =>
    match val.kind with
    | QuotKind.type =>
      pure ("axiom", [])
    | QuotKind.ctor =>
      pure ("axiom", ["Quot"])
    | QuotKind.lift =>
      pure ("axiom", ["Eq", "Quot"])
    | QuotKind.ind =>
      pure ("axiom", ["Quot", "Quot.mk"])
  | _ => pure ("", [])

-- 在 IO 中运行 MetaM
def runMetaMInIO (metaCtx: Meta.Context) (metaState: Meta.State) (coreCtx: Core.Context) (coreStateRef : ST.Ref IO.RealWorld Core.State
)  (constName : String) : IO Unit := do
  let res ← ((getDeps (parseName constName)).run metaCtx metaState coreCtx coreStateRef).toBaseIO
  match res with
  | .ok ((t, deps), _) =>
    IO.println ("\t".intercalate ([t] ++ deps))
  | .error err =>
    let errorMsg ← err.toMessageData.toString
    IO.eprintln s!"Error: {constName} {errorMsg}"

-- 主函数，支持动态交互
def query (constName: String) : IO Unit := do
  let opts : Options := {}
  let env ← importModules #[{ module := `Init }, { module := `Std }] opts
  let coreCtx : Core.Context := {
    options := opts,
    fileName := "<input>",
    fileMap := FileMap.ofString ""
  }
  -- 构造 MetaM.Context
  let lctx : LocalContext := {}
  let metaCtx : Meta.Context := {
    config := {},
    lctx := lctx,
    localInstances := #[],
    defEqCtx? := none
  }
  -- 构造 MetaM.State
  let metaState : Meta.State := {}
  let coreStateRef ← ST.mkRef { env := env } -- 初始化 Core.State
  runMetaMInIO metaCtx metaState coreCtx coreStateRef constName

-- Lean 的入口
def main (args : List String) : IO Unit := do
  -- 检查是否提供了输出目录和文件路径参数
  if args.length == 0 then
    IO.eprintln "Usage: QueryDeps <constName>"
    return
  let constName := args.get! 0
  query constName
