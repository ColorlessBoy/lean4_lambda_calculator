from expr import Expr, Sort, Const, Forall, FVar, Sort0, Sort1, Lambda, Param, mk_normalize_forall, mk_normalize_lambda, App, BoundVar, to_string
from level import mk_normalize_succ_level, mk_normalize_imax_level, is_equivalent as is_equivalent_level

class Calculator:
    def __init__(self):
        self.def_pool: dict[str, Expr] = {}
        self.def_type_pool: dict[str, Expr] = {}
        self.proof_type_pool: dict[str, Expr] = {}

        self.infer_pool: dict[Expr, Expr] = {}
        self.infer_pool_skip_check: dict[Expr, Expr] = {}
    
    # def_expr 会参与到 lambda reduction 中；
    # proof_expr 不会参与到 lambda reduction 中，一个 theorem 被证明后，就可以当成公理直接使用
    def add_definition(self, label: str, type_expr: Expr, def_expr: Expr|None = None, proof_expr: Expr|None = None):
        if label in self.def_type_pool:
            raise ValueError(f"Definition already exists: {label}")
        self.def_type_pool[label] = type_expr
        if def_expr is not None:
            self.def_pool[label] = def_expr
        if proof_expr is not None:
            self.proof_type_pool[label] = proof_expr

    def inst(self, expr: Expr, args: list[Expr], inferOnly=False) -> Expr:
        inst_cache: dict[str, Expr] = {}
        def _inst_aux(expr: Expr, args: list[Expr], offset: int) -> Expr:
            if isinstance(expr, Sort) or isinstance(expr, Const) or isinstance(expr, FVar):
                return expr
            code = str((expr, offset))
            if code in inst_cache:
                return inst_cache[code]
            result = None
            if isinstance(expr, BoundVar):
                if expr.index < len(args):
                    result = args[-1 - expr.index]
                else:
                    result = expr
            if isinstance(expr, Param):
                result = FVar(Param(_inst_aux(expr.type, args, offset), expr.name))
            if isinstance(expr, Forall):
                params = []
                for idx, param in enumerate(expr.params):
                    params.append(Param(_inst_aux(param.type, args, offset+idx)))
                body = _inst_aux(expr.body, args, offset+len(params))
                result = mk_normalize_forall(params, body)
            if isinstance(expr, Lambda):
                params = []
                for idx, param in enumerate(expr.params):
                    params.append(Param(_inst_aux(param.type, args, offset+idx)))
                body = _inst_aux(expr.body, args, offset+len(params))
                result =  mk_normalize_lambda(params, body)
            if isinstance(expr, App):
                func = _inst_aux(expr.func, args, offset)
                args = [_inst_aux(arg, args, offset) for arg in expr.args]
                result = App(func, args)
            if result is None:
                raise ValueError(f"Unsupported expression type: {type(expr)}")
            inst_cache[code] = result
            return result
        return _inst_aux(expr, args, 0)

    def def_eq(self, expr1: Expr, expr2: Expr) -> bool:
        if expr1 is expr2:
            return True
        if hash(expr1) == hash(expr2):
            return True
        if isinstance(expr1, Const):
            if isinstance(expr2, Const) and expr1.label == expr2.label:
                return True
            if expr1.label in self.def_pool:
                return self.def_eq(self.def_pool[expr1.label], expr2)
            else:
                return False # 只定义了类型
        if isinstance(expr2, Const):
            if expr2.label in self.def_pool:
                return self.def_eq(expr1, self.def_pool[expr2.label])
            else:
                return False # 只定义了类型
        if isinstance(expr1, Sort) and isinstance(expr2, Sort) and is_equivalent_level(expr1.level, expr2.level):
            return True
        if isinstance(expr1, BoundVar) and isinstance(expr2, BoundVar) and expr1.index == expr2.index:
            return True
        if isinstance(expr1, Forall) and isinstance(expr2, Forall):
            if len(expr1.params) != len(expr2.params):
                return False
            for param1, param2 in zip(expr1.params, expr2.params):
                if not self.def_eq(param1.type, param2.type):
                    return False
            return self.def_eq(expr1.body, expr2.body)
        if isinstance(expr1, Lambda) and isinstance(expr2, Lambda):
            if len(expr1.params) != len(expr2.params):
                return False
            for param1, param2 in zip(expr1.params, expr2.params):
                if not self.def_eq(param1.type, param2.type):
                    return False
            return self.def_eq(expr1.body, expr2.body)
        # FVar 只能是内存中同一个实例才相等
        if isinstance(expr1, FVar):
            if isinstance(expr2, FVar):
                return expr1.param is expr2.param 
            return expr1.param is expr2
        if isinstance(expr2, FVar):
            return expr2.param is expr1
        return False
    
    def infer(self, expr: Expr, inferOnly=False) -> Expr:
        if not inferOnly and expr in self.infer_pool:
            return self.infer_pool[expr]
        if inferOnly and expr in self.infer_pool_skip_check:
            return self.infer_pool_skip_check[expr]
        if isinstance(expr, FVar):
            return expr.param.type
        if isinstance(expr, Param):
            return expr.type
        if isinstance(expr, Sort):
            return self.infer_sort(expr, inferOnly)
        if isinstance(expr, Const):
            return self.infer_const(expr, inferOnly)
        if isinstance(expr, BoundVar):
            raise ValueError(f"Bound variable is not allowed here: {expr}")
        return expr
    
    def infer_sort(self, expr: Sort, inferOnly=False) -> Sort:
        # TODO: check MVarLevel
        return Sort(mk_normalize_succ_level(expr.level, 1))
    
    def infer_const(self, expr: Const, inferOnly=False) -> Expr:
        if expr.label not in self.def_type_pool:
            raise ValueError(f"Undefined constant: {expr.label}")
        return self.def_type_pool[expr.label]
    
    def ensureForallCore(self, expr: Expr) -> Expr:
        if isinstance(expr, Forall):
            return expr
        return expr
    
    def infer_type(self, norm_expr: Expr, context: list[Expr]=[], inferOnly=False) -> Expr:
        # 希望输入是一个已归一化的表达式
        if isinstance(norm_expr, Sort):
            return Sort(mk_normalize_succ_level(norm_expr.level, 1))
        elif isinstance(norm_expr, Const):
            if norm_expr.label not in self.def_type_pool:
                raise ValueError(f"Undefined constant: {norm_expr.label}")
            return self.def_type_pool[norm_expr.label]
        elif isinstance(norm_expr, BoundVar):
            if norm_expr.index >= len(context):
                raise ValueError(f"Bound variable index out of range: {norm_expr.index}")
            return self.infer_type(self.inst(norm_expr, context, inferOnly), inferOnly)
        elif isinstance(norm_expr, Param):    
            return self.inst(norm_expr.type, context, inferOnly)
        elif isinstance(norm_expr, FVar):
            return norm_expr.param.type
        elif isinstance(norm_expr, Forall):
            new_args = [a for a in context]
            param_types = []
            for index, param in enumerate(norm_expr.params):
                arg_type = self.infer_type(param.type, new_args, inferOnly)
                if isinstance(arg_type, Const) and arg_type.label in self.def_pool and isinstance(self.def_pool[arg_type.label], Sort):
                    arg_type = self.def_pool[arg_type.label]
                if not isinstance(arg_type, Sort):
                    raise TypeError(f"Type of variable must be a Sort, got {param}:{arg_type}")
                if isinstance(param.type, Lambda):
                    raise TypeError(f"Type of variable can not be Lambda, got {param}")
                param_types.append(arg_type)
                new_args.append(self.inst(param, new_args, inferOnly))
            body_type = self.infer_type(norm_expr.body, new_args, inferOnly)
            if isinstance(body_type, Const) and body_type.label in self.def_pool and isinstance(self.def_pool[body_type.label], Sort):
                body_type = self.def_pool[body_type.label]
            if not isinstance(body_type, Sort):
                raise TypeError(f"Body of Forall must be a Sort, got {norm_expr.body}:{body_type}")
            if body_type.level.is_zero():
                return Sort0 # xxx -> (xxx : Sort 0) : Sort 0
            forall_type = body_type
            for arg_type in reversed(param_types):
                if isinstance(arg_type, Const) and arg_type.label in self.def_pool and isinstance(self.def_pool[arg_type.label], Sort):
                    arg_type = self.def_pool[arg_type.label]
                if not isinstance(arg_type, Sort):
                    raise TypeError(f"Type of variable must be a Sort, got {index}-{arg_type}")
                new_level = mk_normalize_imax_level(arg_type.level, forall_type.level)
                if new_level.is_zero():
                    return Sort0
                forall_type = Sort(new_level)
            return forall_type
        elif isinstance(norm_expr, Lambda):
            # 为 Lambda 表达式推断类型
            new_args = [a for a in context]
            for index, param in enumerate(norm_expr.params):
                if isinstance(param.type, Lambda):
                    raise TypeError(f"Type of variable can not be Lambda, got {param}")
                new_args.append(self.inst(param, context, inferOnly)) # 只需要实例化外部的 args
            body_type = self.infer_type(norm_expr.body, new_args, inferOnly)
            return mk_normalize_forall(norm_expr.params, body_type)
        elif isinstance(norm_expr, App):
            func_type = self.infer_type(norm_expr.func, context, inferOnly)
            if not isinstance(func_type, Forall):
                raise TypeError(f"Function in application must have a Forall type, got {norm_expr.func}:{func_type}")
            # 进行类型替换，替换规则是将 func_type.body 中的 func_type.params[i] 替换为 norm_expr.args[i]
            new_args = [a for a in context]
            norm_expr_args = [self.inst(arg, context, inferOnly) for arg in norm_expr.args]
            for index, (param, arg) in enumerate(zip(func_type.params, norm_expr_args)):
                if inferOnly:
                    arg_type = self.infer_type(arg, [], inferOnly)
                    param_type = self.inst(param.type, new_args, inferOnly)
                    if not self.def_eq(arg_type, param_type):
                        raise TypeError(f"Parameter type mismatch: expected {param.type}, got {arg_type}")
                new_args.append(arg)
            new_body = self.inst(func_type.body, new_args, inferOnly)
            if len(func_type.params) == len(norm_expr.args):
                return new_body
            elif len(func_type.params) < len(norm_expr.args):
                return App(new_body, [self.inst(arg, new_args, inferOnly=True) for arg in norm_expr_args[len(func_type.params):]])
            else:
                return mk_normalize_forall(func_type.params[len(norm_expr.args):], new_body)
        raise TypeError(f"Unknown expression type: {norm_expr}")

if __name__ == "__main__":
    calc = Calculator()
    # 定义一个常量 a : Sort 0
    calc.def_pool["Prop"] = Sort0
    calc.def_type_pool["Prop"] = Sort1

    # def Imp := (a:Prop)=>(b:Prop)=>(a->b)
    imp = Lambda([Param(Const("Prop"), "x"), Param(Const("Prop"), "y")], Forall([Param(BoundVar(1))], BoundVar(1)))
    imp_type = calc.infer_type(imp)
    print(f"Imp : {to_string(imp_type)} := {to_string(imp)}")

    iff_type = Forall([Param(Const("Prop")), Param(Const("Prop"))], Const("Prop"))
    print(f"Iff : {to_string(iff_type)}")
    calc.add_definition("Iff", iff_type)

    iff_intro = Forall([Param(Const("Prop"), "a"), Param(Const("Prop"), "b"), Param(Forall([Param(BoundVar(1))], BoundVar(1))), Param(Forall([Param(BoundVar(2))], BoundVar(3)))], App(Const("Iff"), [BoundVar(3), BoundVar(2)]))
    print(f"Iff.intro : {to_string(iff_intro)}")
    calc.add_definition("Iff.intro", iff_intro)

    iff_mp = Forall([Param(Const("Prop"), "a"), Param(Const("Prop"), "b"), Param(App(Const("Iff"), [BoundVar(1), BoundVar(0)])), Param(BoundVar(2))], BoundVar(2))
    print(f"Iff.mp : {to_string(iff_mp)}")
    calc.add_definition("Iff.mp", iff_mp)

    iff_mpr = Forall([Param(Const("Prop"), "a"), Param(Const("Prop"), "b"), Param(App(Const("Iff"), [BoundVar(1), BoundVar(0)])), Param(BoundVar(1))], BoundVar(3))
    print(f"Iff.mpr : {to_string(iff_mpr)}")
    calc.add_definition("Iff.mpr", iff_mpr)

    id = Lambda([Param(Const("Prop"), "h"), Param(BoundVar(0), "a")], BoundVar(0))
    id_type = calc.infer_type(id)
    print(f"id : {to_string(id_type)} := {to_string(id)}")
    calc.add_definition("id", id_type, id)

    iff_refl = Lambda([Param(Const("Prop"), "a")], App(Const("Iff.intro"), [BoundVar(0), BoundVar(0), App(Const("id"), [BoundVar(0)]), App(Const("id"), [BoundVar(0)])]))
    iff_refl_type = calc.infer_type(iff_refl)
    print(f"Iff.refl : {to_string(iff_refl_type)} := {to_string(iff_refl)}")
    calc.add_definition("Iff.refl", iff_refl_type, proof_expr=iff_refl)

    and_type = Forall([Param(Const("Prop"), "left"), Param(Const("Prop"), "right")], Const("Prop"))
    print(f"And : {to_string(and_type)}")
    calc.add_definition("And", and_type)

    and_intro = Forall([Param(Const("Prop"), "left"), Param(Const("Prop"), "right"), Param(BoundVar(1)), Param(BoundVar(1))], App(Const("And"), [BoundVar(3), BoundVar(2)]))
    print(f"And.intro : {to_string(and_intro)}")
    calc.add_definition("And.intro", and_intro)

    and_left = Forall([Param(Const("Prop"), "left"), Param(Const("Prop"), "right"), Param(App(Const("And"), [BoundVar(1), BoundVar(0)]))], BoundVar(2))
    print(f"And.left : {to_string(and_left)}")

    and_right = Forall([Param(Const("Prop"), "left"), Param(Const("Prop"), "right"), Param(App(Const("And"), [BoundVar(1), BoundVar(0)]))], BoundVar(1))
    print(f"And.right : {to_string(and_right)}")

    or_type = Forall([Param(Const("Prop"), "left"), Param(Const("Prop"), "right")], Const("Prop"))
    print(f"Or : {to_string(or_type)}")
    calc.add_definition("Or", or_type)

    or_inl = Forall([Param(Const("Prop"), "left"), Param(Const("Prop"), "right"), Param(BoundVar(1))], App(Const("Or"), [BoundVar(2), BoundVar(1)]))
    print(f"Or.inl : {to_string(or_inl)}")
    calc.add_definition("Or.inl", or_inl)

    or_inr = Forall([Param(Const("Prop"), "left"), Param(Const("Prop"), "right"), Param(BoundVar(0))], App(Const("Or"), [BoundVar(2), BoundVar(1)]))
    print(f"Or.inr : {to_string(or_inr)}")
    calc.add_definition("Or.inr", or_inr)

    # def Or.rec : (a : Prop) -> (b : Prop) -> (motive : Or a b -> Prop) -> ((ha : a) -> motive (Or.inl a b ha)) -> ((hb : b) -> motive (Or.inr a b hb)) -> (h : Or a b) -> motive h
    left = Param(Const("Prop"), "left")
    right = Param(Const("Prop"), "right")
    motive = Param(Forall([Param(App(Const("Or"), [BoundVar(1), BoundVar(0)]))], Const("Prop")), "motive")
    hl = Param(Forall([Param(BoundVar(2), "hl")], App(BoundVar(1), [App(Const("Or.inl"), [BoundVar(3), BoundVar(2), BoundVar(0)])]))) 
    hr = Param(Forall([Param(BoundVar(2), "hr")], App(BoundVar(2), [App(Const("Or.inr"), [BoundVar(4), BoundVar(3), BoundVar(0)])]))) 
    hor = Param(App(Const("Or"), [BoundVar(4), BoundVar(3)]), "h")
    body = App(BoundVar(3), [BoundVar(0)])
    or_rec = Forall([left, right, motive, hl, hr, hor], body)
    print(f"Or.rec : {to_string(or_rec)}")
    calc.add_definition("Or.rec", or_rec)

    # thm Or.elim : (a:Prop)->(b:Prop)->(c:Prop)->Or a b->(a->c)->(b->c)->c
    # (a : Prop) => (b : Prop) => (c : Prop) => (h1 : Or a b) => (h2 : a -> c) => (h3 : b -> c) => Or.rec a b (Or a b => c) h2 h3 h1  
    # Ensure all arguments are wrapped as Expr instances
    or_elim = Lambda([
        Param(Const("Prop"), "a"), 
        Param(Const("Prop"), "b"), 
        Param(Const("Prop"), "c"), 
        Param(App(Const("Or"), [BoundVar(1), BoundVar(0)]), "h1"),
        Param(Forall([Param(BoundVar(3))], BoundVar(2)), "h2"), 
        Param(Forall([Param(BoundVar(3))], BoundVar(3)), "h3"), 
    ], App(
        Const("Or.rec"), 
        [
            BoundVar(5), 
            BoundVar(4), 
            Lambda([Param(App(Const("Or"), [BoundVar(5), BoundVar(4)]))], BoundVar(4)), 
            BoundVar(1), 
            BoundVar(0), 
            BoundVar(2)
        ]
    ))
    print(f"Or.elim : {to_string(or_elim)}")
    or_elim_type = calc.infer_type(or_elim)
    print(f"Or.elim : {to_string(or_elim_type)} := {to_string(or_elim)}")
    calc.add_definition("Or.elim", or_elim_type, proof_expr=or_elim)
