
from parser import load_thm, parse_expr, ThmsPool, calc, Expr, Lambda, Forall, App, Const
from calculator import VarType, shift_context, BoundVar, shift_expr

def split(target: Expr, proof: Expr, context: list[VarType], thmspool: ThmsPool):
    if isinstance(proof, Lambda):
        assert isinstance(target, Forall), "proof is Lambda, but target is not Forall"
        # var_type, _ = calc(proof.var_type, context, thmspool.type_pool, thmspool.def_pool)
        assert target.var_type == proof.var_type, f"Type mismatch: want\n  {target.var_type}\nget\n  {proof.var_type}\n\n"
        shifted_var_type = shift_expr(proof.var_type)
        shifted_context = [(BoundVar(0), shifted_var_type)] + shift_context(context)
        action, next_states = split(target.body, proof.body, shifted_context, thmspool=thmspool)
        return_action = Lambda(proof.var_type, action)
        return_states = []
        for ns, a in next_states:
            return_states.append((Forall(proof.var_type, ns), Lambda(proof.var_type, a)))
        return return_action, return_states
    elif isinstance(proof, App):
        if isinstance(proof.func, Const) or isinstance(proof.func, BoundVar):
            if isinstance(proof.arg, Const) or isinstance(proof.arg, BoundVar):
                return proof, []
            arg, arg_type = calc(proof.arg, context, thmspool.type_pool, thmspool.def_pool)
            arg_action, next_states = split(arg_type, proof.arg, [], thmspool)
            return App(proof.func, arg_action), next_states
        func, func_type = calc(proof.func, context, thmspool.type_pool, thmspool.def_pool)
        if isinstance(proof.arg, Const) or isinstance(proof.arg, BoundVar):
            func_action, next_states = split(func_type, proof.func, [], thmspool)
            return App(func_action, proof.arg), next_states
        arg, arg_type = calc(proof.arg, context, thmspool.type_pool, thmspool.def_pool)
        shifted_arg_type = shift_expr(arg_type)
        return Lambda(func_type, Lambda(shifted_arg_type, App(BoundVar(1), BoundVar(0)))), [(func_type, proof.func), (arg_type, proof.arg)]
    return proof, []

def dfs_split(target: Expr, proof: Expr, thmspool: ThmsPool):
    action, next_states  = split(target, proof, [], thmspool)
    print()
    print("STATES:\n", target)
    print("ACTION:\n", action)
    print("STATES:\n", next_states)

    for next_target, next_proof in next_states:
        dfs_split(next_target, next_proof, thmspool)

# 测试代码
if __name__ == "__main__":
    # thmname = "Iff.refl"
    thmname = "mul_le_mul_left"
    _, target, proof = load_thm(thmname)
    parsed_target = parse_expr(target)
    print(f"{thmname} target:\n  {parsed_target}")
    parsed_proof = parse_expr(proof)
    print(f"{thmname} proof:\n  {parsed_proof}")

    thmspool = ThmsPool()
    thmspool.update(parsed_target)
    thmspool.update(parsed_proof)

    dfs_split(parsed_target, parsed_proof, thmspool)
