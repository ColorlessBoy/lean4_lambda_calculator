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

def getPreferenceLevel (e : Expr) : Nat :=
  match e with
  | Expr.bvar _ => 100
  | Expr.fvar _ => 100
  | Expr.mvar _ => 100
  | Expr.sort _ => 3
  | Expr.const _ _ => 100
  | Expr.app _ _=> 4
  | Expr.forallE _ _ _ _ => 2
  | Expr.lam _ _ _ _ => 1
  | Expr.letE _ _ _ _ _ => 100
  | Expr.lit _ => 100
  | Expr.mdata _ expr => getPreferenceLevel expr
  | Expr.proj _ _ _ => 100

def printLevel (lvl : Level) : MetaM String := do
  match lvl with
  | Level.zero   => pure s!"0"
  | Level.succ l =>
    let pre ← printLevel l
    pure s!"({pre} + 1)"
  | Level.max l r =>
    let l ← printLevel l
    let r ← printLevel r
    pure s!"(max {l} {r})"
  | Level.imax l r =>
    let l ← printLevel l
    let r ← printLevel r
    pure s!"(imax {l} {r})"
  | Level.param name => pure s!"{name}"
  | Level.mvar id => pure s!"{id.name}"

def _cleanName (name : Name) (context : List String) : String :=
  let nameStr := s!"{name}"
  let baseName := match nameStr.split (fun c => c = '.') with
    | [] => nameStr
    | hd :: _ => hd
  if context.length == 0 then
    baseName
  else
  -- 递归地添加后缀数字，直到名字不在 context 中
  let rec getUniqueName (suffix : Nat) (base : String) : String :=
    match suffix with
    | Nat.zero => s!"{base}{context.length}"
    | Nat.succ pre =>
      let idx := context.length - suffix
      let candidate := if idx == 0 then base else s!"{base}{idx}"
      if candidate ∈ context then
        getUniqueName pre base
      else
        candidate
  getUniqueName context.length baseName

def _isBinderUsed (body : Expr) (offset : Nat := 0) : Bool :=
  match body with
  | Expr.bvar idx => idx == offset
  | Expr.app f arg => _isBinderUsed f offset || _isBinderUsed arg offset
  | Expr.lam _ ty body _ | Expr.forallE _ ty body _ =>
    _isBinderUsed ty offset || _isBinderUsed body (offset + 1)
  | Expr.letE _ _ value body _ =>
    _isBinderUsed value offset || _isBinderUsed body (offset + 1)
  | _ => false

def _transformExpr (expr : Expr) (context : List String) : MetaM String := do
  match expr with
  | Expr.bvar idx => pure context[idx]!
  | Expr.fvar fId => pure s!"{← fId.getUserName}"
  | Expr.mvar _ => pure s!"{expr}"
  | Expr.sort lvl =>
    match lvl with
    | Level.zero   => pure "Prop"
    | Level.succ prelvl   =>
      let slvl ← printLevel prelvl
      pure s!"Type {slvl}"
    | _      =>
      let slvl ← printLevel lvl
      pure s!"Sort {slvl}"
  | Expr.const name _ => pure s!"{name}"
  | Expr.app f arg =>
    let mut fStr ← _transformExpr f context
    let mut argStr ← _transformExpr arg context
    let expr_level := getPreferenceLevel expr
    let f_level := getPreferenceLevel f
    let arg_level := getPreferenceLevel arg
    if fStr != "Prop" && fStr != "Type" && f_level < expr_level then
      fStr := s!"({fStr})"
    fStr := match f with
    | Expr.const _ _ => s!"@{fStr}"
    | _ => fStr
    if argStr != "Prop" && argStr != "Type" && arg_level <= expr_level then
      argStr := s!"({argStr})"
    pure s!"{fStr} {argStr}"
  | Expr.lam name ty body bindInfo =>
    let name := _cleanName name context
    let tyStr ← _transformExpr ty context
    let mut bodyStr ← _transformExpr body ([s!"{name}"] ++ context)
    let expr_level := getPreferenceLevel expr
    let body_level := getPreferenceLevel body
    if body_level < expr_level then
      bodyStr := s!"({bodyStr})"
    let mut argStr := s!"{name} : {tyStr}"
    if !(_isBinderUsed body) then
      argStr := s!"_ : {tyStr}"
    if bindInfo.isImplicit then
      argStr := "{" ++ argStr ++ "}"
    else
      argStr := s!"({argStr})"
    pure s!"fun {argStr} => {bodyStr}"
  | Expr.forallE name ty body bindInfo =>
    let name := _cleanName name context
    let tyStr ← _transformExpr ty context
    let mut bodyStr ← _transformExpr body ([s!"{name}"] ++ context)
    let exprLevel := getPreferenceLevel expr
    let bodyLevel := getPreferenceLevel body
    if bodyLevel < exprLevel then
      bodyStr := s!"({bodyStr})"
    let mut argStr := s!"{name} : {tyStr}"
    if !(_isBinderUsed body) then
      let typeLevel := getPreferenceLevel ty
      if typeLevel <= exprLevel then
        argStr := s!"({tyStr})"
      else
        argStr := s!"{tyStr}"
    else
      if bindInfo.isImplicit then
        argStr := "{" ++ argStr ++ "}"
      else
        argStr := s!"({argStr})"
    pure s!"{argStr} -> {bodyStr}"
  | Expr.letE name _ value body _ =>
    let name := _cleanName name context
    let value ← _transformExpr value context
    let body ← _transformExpr body ([name] ++ context)
    pure s!"(let {name} := {value} ; {body})"
  | Expr.lit _ => pure s!"({expr})"
  | Expr.mdata _ _ => pure s!"({expr})"
  | Expr.proj _ _ _ => pure s!"({expr})"

def transformExpr (name : Name) : MetaM String := do
  let env ← getEnv
  match env.find? name with
  | some (ConstantInfo.axiomInfo ax) =>
    -- 公理：只有类型，没有值
    let typeStr ← _transformExpr ax.type []
    pure s!"axiom {name} : {typeStr}"
  | some (ConstantInfo.thmInfo thm) =>
    -- 定理：有类型和证明值
    let typeStr ← _transformExpr thm.type []
    let valueStr ← _transformExpr thm.value []
    pure s!"theorem {name} : {typeStr} := \n  {valueStr}"
  | some (ConstantInfo.defnInfo defn) =>
    -- 定义：有类型和定义体
    let typeStr ← _transformExpr defn.type []
    let valueStr ← _transformExpr defn.value []
    pure s!"def {name} : {typeStr} := \n  {valueStr}"
  | some (ConstantInfo.ctorInfo ctor) =>
    -- 构造函数：有类型，但无单独定义值
    let typeStr ← _transformExpr ctor.type []
    pure s!"axiom {ctor.name} : {typeStr}"
  | some (ConstantInfo.recInfo rec) =>
    -- 消去规则（recursor）：有类型，但无定义值
    let typeStr ← _transformExpr rec.type []
    pure s!"axiom {rec.name} : {typeStr}"
  | some (ConstantInfo.inductInfo ind) =>
    -- 归纳定义：有类型，但无定义值
    let typeStr ← _transformExpr ind.type []
    pure s!"axiom {ind.name} : {typeStr}"
  | some (ConstantInfo.opaqueInfo val) =>
    let typeStr ← _transformExpr val.value []
    pure s!"axiom {val.name} : {typeStr}"
  | some (ConstantInfo.quotInfo val) =>
    match val.kind with
    | QuotKind.type =>
      pure "axiom Quot : {α : Sort u} -> (α -> α -> Prop) -> Sort u"
    | QuotKind.ctor =>
      pure "axiom Quot.mk : {α : Sort u} -> (r : α -> α -> Prop) -> α -> @Quot α r"
    | QuotKind.lift =>
      pure "axiom Quot.lift : {α : Sort u} -> {r : α -> α -> Prop} -> {β : Sort v} -> (f : α -> β) -> ((a : α) -> (b : α) -> r a b -> @Eq β (f a) (f b)) -> @Quot α r -> β"
    | QuotKind.ind =>
      pure "axiom Quot.ind : {α : Sort u} -> {r : α -> α -> Prop} -> {β : @Quot α r -> Prop} -> ((a : α) -> β (@Quot.mk α r a)) -> (q : @Quot α r) -> β q"
  | _ => throwError "Constant {name} not found or is not supported."

-- 在 IO 中运行 MetaM
def runMetaMInIO (metaCtx: Meta.Context) (metaState: Meta.State) (coreCtx: Core.Context) (coreStateRef : ST.Ref IO.RealWorld Core.State
)  (constName : String) : IO Unit := do
  let res ← ((transformExpr (parseName constName)).run metaCtx metaState coreCtx coreStateRef).toBaseIO
  match res with
  | .ok (info, _) =>
    IO.println info
  | .error err =>
    let errorMsg ← err.toMessageData.toString
    IO.println s!"Error: {constName} {errorMsg}"

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
    IO.println "Usage: QueryConst <constName>"
    return
  let constName := args.get! 0
  query constName
