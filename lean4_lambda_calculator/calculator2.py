from expr import Expr, Sort, Const, Forall, Sort0, Sort1, Lambda, Param, mk_normalize_forall, mk_normalize_lambda, App, BoundVar, to_string
from level import mk_normalize_succ_level, mk_normalize_imax_level, is_equivalent as is_equivalent_level

class Calculator:
    def __init__(self):
        self.def_pool: dict[str, Expr] = {}
        self.def_type_pool: dict[str, Expr] = {}
        self.proof_type_pool: dict[str, Expr] = {}
    
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

    def _offset(self, expr: Expr, offset: int) -> Expr:
        if offset == 0:
            return expr
        if isinstance(expr, Sort) or isinstance(expr, Const):
            return expr
        if isinstance(expr, Param):
            return Param(self._offset(expr.type, offset), expr.name)
        if isinstance(expr, App):
            return App(self._offset(expr.func, offset), [self._offset(a, offset) for a in expr.args])
        if isinstance(expr, Lambda):
            shifted_params = [Param(self._offset(param.type, offset), param.name) for param in expr.params]
            shifted_body = self._offset(expr.body, offset)
            return Lambda(shifted_params, shifted_body)
        if isinstance(expr, Forall):
            shifted_params = [Param(self._offset(param.type, offset), param.name) for param in expr.params]
            shifted_body = self._offset(expr.body, offset)
            return Forall(shifted_params, shifted_body)
        if isinstance(expr, BoundVar):
            return BoundVar(expr.index+offset)
        raise ValueError(f"Unsupported expression type: {type(expr)}")

    def app_reduce(self, expr: App, outer_args: list[Expr], outer_arg_types: list[Expr], checking=False) -> Expr:
        assert len(outer_arg_types) == len(outer_args)
        func, args = expr.func, expr.args 
        while isinstance(func, Lambda) or (isinstance(func, Const) and func.label in self.def_pool and isinstance(self.def_pool[func.label], Lambda)):
            if isinstance(func, Const):
                func = self.def_pool[func.label] 
            assert isinstance(func, Lambda), "func must be Lambda"
            new_args = []
            new_arg_types = []
            for param, arg in zip(func.params, args):
                arg_type = self.infer_type(arg, outer_args+new_args, outer_arg_types+new_arg_types)
                if checking and not self.def_eq(param.type, arg_type):
                    raise TypeError(f"Parameter type mismatch: expected {param.type}, got {arg_type}")
            if len(func.params) > len(args):
                new_args.extend(func.params[len(args):])
                new_arg_types.extend([p.type for p in func.params[len(args):]])
            new_body = self.substitute(func.body, outer_args + new_args, outer_arg_types + new_arg_types, checking)
            if len(args) < len(func.params):
                return mk_normalize_lambda(func.params[len(args):], new_body)
            elif len(args) > len(func.params):
                func, args = new_body, outer_args[len(func.params):]
            else:
                return new_body
        return App(func, args)
        
    
    def substitute(self, expr: Expr, outer_args: list[Expr], outer_arg_types: list[Expr], checking=False) -> Expr:
        assert len(outer_arg_types) == len(outer_args)
        if isinstance(expr, BoundVar):
            if expr.index >= len(outer_args):
                raise ValueError(f"Bound variable index out of range: {expr.index}")
            arg = outer_args[-1 - expr.index]
            if isinstance(arg, Param):
                cnt = 0
                for i in range(len(outer_args)-1, expr.index-1, -1):
                    if isinstance(outer_args[i], Param):
                        cnt += 1
                return BoundVar(cnt)
            return arg
        elif isinstance(expr, App):
            expr = App(self.substitute(expr.func, outer_args, outer_arg_types, checking), [self.substitute(a, outer_args, outer_arg_types, checking) for a in expr.args])
            expr_reduce = self.app_reduce(expr, outer_args, outer_arg_types, checking)
            return expr_reduce
        elif isinstance(expr, Lambda):
            new_params = []
            new_param_types = []
            for param in expr.params:
                t = self.substitute(param.type, outer_args+new_params, outer_arg_types=outer_arg_types+new_param_types, checking=checking)
                new_params.append(Param(t, param.name))
            new_body = self.substitute(expr.body, outer_args+new_params, outer_arg_types+new_param_types, checking=checking)
            return mk_normalize_lambda(new_params, new_body)
        elif isinstance(expr, Forall):
            new_params = []
            new_param_types = []
            for param in expr.params:
                t = self.substitute(param.type, outer_args+new_params, outer_arg_types+new_param_types, checking=checking)
                new_param_types.append(t)
                new_params.append(Param(t, param.name))
            new_body = self.substitute(expr.body, outer_args+new_params, outer_arg_types+new_param_types, checking=checking)
            return mk_normalize_forall(new_params, new_body)
        elif isinstance(expr, Param):
            return Param(self.substitute(expr.type, outer_args, outer_arg_types, checking), expr.name)
        return expr
    
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
        return False
    
    def infer_type(self, norm_expr: Expr, outer_args: list[Expr]=[], outer_arg_types: list[Expr]=[], checking=False) -> Expr:
        # 希望输入是一个已归一化的表达式
        if isinstance(norm_expr, Sort):
            return Sort(mk_normalize_succ_level(norm_expr.level, 1))
        elif isinstance(norm_expr, Const):
            if norm_expr.label not in self.def_type_pool:
                raise ValueError(f"Undefined constant: {norm_expr.label}")
            return self.def_type_pool[norm_expr.label]
        elif isinstance(norm_expr, BoundVar):
            if norm_expr.index >= len(outer_arg_types):
                raise ValueError(f"Bound variable index out of range: {norm_expr.index}")
            expr = outer_arg_types[-1 - norm_expr.index]
            expr_offset = self._offset(expr, len(outer_arg_types)-norm_expr.index-1)
            return expr_offset
        elif isinstance(norm_expr, Param):    
            return norm_expr.type
        elif isinstance(norm_expr, Forall):
            new_args = [a for a in outer_args]
            new_arg_types = [t for t in outer_arg_types]
            for index, param in enumerate(norm_expr.params):
                param_type = self.infer_type(param.type, new_args, new_arg_types, checking)
                if isinstance(param_type, Const) and param_type.label in self.def_pool and isinstance(self.def_pool[param_type.label], Sort):
                    param_type = self.def_pool[param_type.label]
                if not isinstance(param_type, Sort):
                    raise TypeError(f"Type of variable must be a Sort, got {param}:{param_type}")
                if isinstance(param.type, Lambda):
                    raise TypeError(f"Type of variable can not be Lambda, got {param}")
                new_args.append(param)
                new_arg_types.append(param_type)
            body_type = self.infer_type(norm_expr.body, new_args, new_arg_types, checking)
            if isinstance(body_type, Const) and body_type.label in self.def_pool and isinstance(self.def_pool[body_type.label], Sort):
                body_type = self.def_pool[body_type.label]
            if not isinstance(body_type, Sort):
                raise TypeError(f"Body of Forall must be a Sort, got {norm_expr.body}:{body_type}")
            if body_type.level.is_zero():
                return Sort0 # xxx -> (xxx : Sort 0) : Sort 0
            forall_type = body_type
            for index in range(len(new_arg_types) - 1, len(outer_arg_types) - 1, -1):
                arg_type = new_arg_types[index]
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
            new_args = [a for a in outer_args]
            new_arg_types = [t for t in outer_arg_types]
            for index, param in enumerate(norm_expr.params):
                if isinstance(param.type, Lambda):
                    raise TypeError(f"Type of variable can not be Lambda, got {param}")
                new_args.append(param)
                new_arg_types.append(param.type)
            body_type = self.infer_type(norm_expr.body, new_args, new_arg_types, checking)
            return mk_normalize_forall(norm_expr.params, body_type)
        elif isinstance(norm_expr, App):
            func_type = self.infer_type(norm_expr.func, outer_args, outer_arg_types, checking)
            if not isinstance(func_type, Forall):
                raise TypeError(f"Function in application must have a Forall type, got {norm_expr.func}:{func_type}")
            if len(func_type.params) < len(norm_expr.args):
                raise TypeError(f"Parameter length mismatch: expected {len(norm_expr.args)}, got {len(func_type.params)}")
            # 进行类型替换，替换规则是将 func_type.body 中的 func_type.params[i] 替换为 norm_expr.args[i]
            new_arg_types = [t for t in outer_arg_types]
            new_args = [a for a in outer_args]
            for index, (param, arg) in enumerate(zip(func_type.params, norm_expr.args)):
                arg_type = self.infer_type(arg, outer_args, outer_arg_types, checking)
                new_param_type = self.substitute(param.type, new_args, new_arg_types, checking)
                if not self.def_eq(arg_type, new_param_type):
                    raise TypeError(f"Parameter type mismatch: expected {param.type}, got {arg_type}")
                new_arg_types.append(arg_type)
                if index < len(norm_expr.args):
                    new_args.append(arg)
                else: 
                    new_args.append(param)
            new_body = self.substitute(func_type.body, new_args, new_arg_types, checking)
            if len(func_type.params) == len(norm_expr.args):
                return new_body
            elif len(func_type.params) < len(norm_expr.args):
                return App(new_body, norm_expr.args[len(func_type.params):])
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
