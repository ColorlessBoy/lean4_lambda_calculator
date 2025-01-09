import Lean
import Lean.Meta
import Std.Data.HashMap

open Lean Meta Tactic
open Lean System Meta

-- 计算 Expr 的节点数，深度超过 maxSearchSize 时提前终止，返回 1
partial def getExprSize (e : Expr) (reward : Nat) : Nat :=
  if reward <= 0 then
    1 -- 超过最大深度，提前返回 1
  else
    match e with
    | Expr.bvar _ => 1
    | Expr.fvar _ => 1
    | Expr.mvar _ => 1
    | Expr.sort _ => 1
    | Expr.const _ _ => 1
    | Expr.app f arg =>
      let n1 := getExprSize f (reward - 1)
      let n2 := getExprSize arg (reward - n1 - 1)
      1 + n1 + n2
    | Expr.lam _ t body _ =>
      let n1 := getExprSize t (reward - 1)
      let n2 := getExprSize body (reward - n1 - 1)
      1 + n1 + n2
    | Expr.forallE _ t body _ =>
      let n1 := getExprSize t (reward - 1)
      let n2 := getExprSize body (reward - n1 - 1)
      1 + n1 + n2
    | Expr.letE _ t val body _ =>
      let n1 := getExprSize t (reward - 1)
      let n2 := getExprSize val (reward - n1 - 1)
      let n3 := getExprSize body (reward - n1 - n2 - 1)
      1 + n1 + n2 + n3
    | Expr.lit _ => 1
    | Expr.mdata _ e => 1 + getExprSize e (reward - 1)
    | Expr.proj _ _ e => 1 + getExprSize e (reward - 1)

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

def getPrefixLevel (e : Expr) : Nat :=
  match e with
  | Expr.bvar _ => 100
  | Expr.fvar _ => 100
  | Expr.mvar _ => 100
  | Expr.sort _ => 100
  | Expr.const _ _ => 100
  | Expr.app _ _=> 3
  | Expr.lam _ _ _ _ => 2
  | Expr.forallE _ _ _ _ => 1
  | Expr.letE _ _ _ _ _ => 100
  | Expr.lit _ => 100
  | Expr.mdata _ _ => 100
  | Expr.proj _ _ _ => 100

-- 将表达式转化为前缀表达式的字符串
partial def toPrefixExpr (e : Expr) (maxExprSize: Nat) : MetaM String := do
  let size := getExprSize e maxExprSize
  if size >= maxExprSize then
    return s!"Too large"
  match e with
  | Expr.bvar idx => pure s!"#{idx}"
  | Expr.fvar fvarId => pure s!"(FreeVar {fvarId.name})"
  | Expr.mvar mvarId => pure s!"(MetaVar {mvarId.name})"
  | Expr.sort lvl =>
    if lvl == 0 then
      return "Prop"
    pure s!"Sort({lvl})"
  | Expr.const n _ => pure s!"{n}"
  | Expr.app f arg =>
    let mut fStr ← toPrefixExpr f maxExprSize
    let mut argsStr ← toPrefixExpr arg maxExprSize
    let expr_level := getPrefixLevel e
    let f_level := getPrefixLevel f
    let arg_level := getPrefixLevel arg
    if f_level < expr_level then
      fStr := s!"({fStr})"
    if arg_level <= expr_level then
      argsStr := s!"({argsStr})"
    pure s!"{fStr} {argsStr}"
  | Expr.lam _ t body _ =>
    let mut bodyStr ← toPrefixExpr body maxExprSize
    let mut t_prefix ← toPrefixExpr t maxExprSize
    let expr_level := getPrefixLevel e
    let t_level := getPrefixLevel t
    let arg_level := getPrefixLevel body
    if t_level <= expr_level then
      t_prefix := s!"({t_prefix})"
    if arg_level < expr_level then
      bodyStr := s!"({bodyStr})"
    pure s!"{t_prefix} => {bodyStr}"
  | Expr.forallE _ t body _ =>
    let mut bodyStr ← toPrefixExpr body maxExprSize
    let mut t_prefix ← toPrefixExpr t maxExprSize
    let expr_level := getPrefixLevel e
    let t_level := getPrefixLevel t
    let arg_level := getPrefixLevel body
    if t_level <= expr_level then
      t_prefix := s!"({t_prefix})"
    if arg_level < expr_level then
      bodyStr := s!"({bodyStr})"
    pure s!"{t_prefix} -> {bodyStr}"
  | Expr.letE n t value body _ => do
    let tStr ← toPrefixExpr t maxExprSize
    let valueStr ← toPrefixExpr value maxExprSize
    let bodyStr ← toPrefixExpr body maxExprSize
    pure s!"(Let ({n} : {tStr}) := {valueStr}; {bodyStr})"
  | Expr.lit l =>
    match l with
    | Literal.natVal val => pure s!"(NatLiteral {val})"
    | Literal.strVal val => pure s!"(StrLiteral \"{val}\")"
  | Expr.mdata data expr =>
    let bodyExpr ← toPrefixExpr expr maxExprSize
    pure s!"(Mdata {data} :: {bodyExpr})"
  | Expr.proj typeName idx struct =>
    let prefixStruct ← toPrefixExpr struct maxExprSize
    pure s!"(Proj {typeName} {idx} {prefixStruct})"


-- 提取常量的信息
def getConstantDetails (name : Name)  (maxPropSize : Nat) (maxProofSize : Nat): MetaM String := do
  let env ← getEnv
  match env.find? name with
  | some (ConstantInfo.axiomInfo ax) =>
      -- 公理：只有类型，没有值
      let name := s!"{ax.name}"
      let type ← toPrefixExpr ax.type maxPropSize
      pure s!"def {name} : {type}"
  | some (ConstantInfo.thmInfo thm) =>
      -- 定理：有类型和证明值
      let name := s!"{thm.name}"
      let type ← toPrefixExpr thm.type maxPropSize
      let proof ← toPrefixExpr thm.value maxProofSize
      pure s!"thm {name} : {type}\n  {proof}"
  | some (ConstantInfo.defnInfo defn) =>
      -- 定义：有类型和定义体
      let name := s!"{defn.name}"
      let value ← toPrefixExpr defn.value maxPropSize
      pure s!"def {name} = {value}"
  | some (ConstantInfo.ctorInfo ctor) =>
      -- 构造函数：有类型，但无单独定义值
      let name := s!"{ctor.name}"
      let type ← toPrefixExpr ctor.type maxPropSize
      pure s!"def {name} : {type}"
  | some (ConstantInfo.recInfo rec) =>
      -- 消去规则（recursor）：有类型，但无定义值
      let name := s!"{rec.name}"
      let type ← toPrefixExpr rec.type maxPropSize
      pure s!"def {name} : {type}"
  | some (ConstantInfo.inductInfo ind) =>
      -- 归纳定义：有类型，但无定义值
      let name := s!"{ind.name}"
      let type ← toPrefixExpr ind.type maxPropSize
      pure s!"def {name} : {type}"
  | _ => pure ""

-- 在 IO 中运行 MetaM
def runMetaMInIO (metaCtx: Meta.Context) (metaState: Meta.State) (coreCtx: Core.Context) (coreStateRef : ST.Ref IO.RealWorld Core.State
)  (constName : String) (maxPropSize: Nat) (maxProofSize: Nat) : IO Unit := do
  let res ← ((getConstantDetails (parseName constName) maxPropSize maxProofSize).run metaCtx metaState coreCtx coreStateRef).toBaseIO
  match res with
  | .ok (info, _) =>
    IO.println info
  | .error err =>
    let errorMsg ← err.toMessageData.toString
    IO.println s!"Error: {constName} {errorMsg}"

-- 主函数，支持动态交互
def query (constName: String) (maxPropSize: Nat) (maxProofSize: Nat) : IO Unit := do
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
  runMetaMInIO metaCtx metaState coreCtx coreStateRef constName maxPropSize maxProofSize

-- Lean 的入口
def main (args : List String) : IO Unit := do
  -- 检查是否提供了输出目录和文件路径参数
  if args.length == 0 then
    IO.println "Usage: QueryConst <constName> ?<maxPropSize> ?<maxProofSize>"
    return

  let constName := args.get! 0
  let maxPropSize := if args.length > 1 then (args.get! 1).toNat! else 10000
  let maxProofSize := if args.length > 2 then (args.get! 2).toNat! else 10000
  query constName maxPropSize maxProofSize
