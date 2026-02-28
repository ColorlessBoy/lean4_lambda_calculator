# 这个文件定义了 Lean 4 中的 level 相关的类和函数，用于表示和比较 universe levels。
import math
from functools import cmp_to_key


class Level:
    def __init__(self, level: str | int) -> None:
        raise NotImplementedError(
            "Level is an abstract class, cannot be instantiated directly."
        )

    def __hash__(self) -> int:
        return hash(repr(self))

    def is_constant(self) -> bool:
        return (
            not math.isinf(self.upper_bound())
            and self.lower_bound() == self.upper_bound()
        )

    def lower_bound(self) -> float:
        return 0

    def upper_bound(self) -> float:
        return math.inf

    def is_zero(self) -> bool:
        return self.upper_bound() == 0

    def is_one(self) -> bool:
        return self.is_constant() and self.upper_bound() == 1


class ParamLevel(Level):
    def __init__(self, name: str) -> None:
        self.name = name

    def __repr__(self) -> str:
        return self.name


class MVarLevel(Level):
    def __init__(self, name: str) -> None:
        self.name = name

    def __repr__(self) -> str:
        return f"?{self.name}"


class NatLevel(Level):
    def __init__(self, value: int) -> None:
        self.value = value

    def __repr__(self) -> str:
        return str(self.value)

    def is_constant(self) -> bool:
        return True

    def lower_bound(self) -> float:
        return self.value

    def upper_bound(self) -> float:
        return self.value


class SuccLevel(Level):
    def __init__(self, level: Level, offset: int = 1) -> None:
        assert offset > 0, "Depth must be a positive integer."
        self.level = level
        self.offset = offset

    def __repr__(self) -> str:
        return f"{self.level}+{self.offset}"

    def lower_bound(self) -> float:
        return self.level.lower_bound() + self.offset

    def upper_bound(self) -> float:
        return self.level.upper_bound() + self.offset


class MaxLevel(Level):
    def __init__(self, levels: list[Level]) -> None:
        self.levels = levels

    def __repr__(self) -> str:
        return "Max(" + ", ".join(repr(level) for level in self.levels) + ")"

    def lower_bound(self) -> float:
        return max(level.lower_bound() for level in self.levels)

    def upper_bound(self) -> float:
        return max(level.upper_bound() for level in self.levels)


class IMaxLevel(Level):
    def __init__(self, left: Level, right: Level) -> None:
        self.left = left
        self.right = right

    def __repr__(self) -> str:
        return f"IMax({self.left}, {self.right})"

    def lower_bound(self) -> float:
        if self.right.lower_bound() == 0:
            return 0
        return max(self.left.lower_bound(), self.right.lower_bound())

    def upper_bound(self) -> float:
        if self.right.upper_bound() == 0:
            return 0
        return max(self.left.upper_bound(), self.right.upper_bound())


# 相等的充分条件：is_sufficient_equal 为 True，则 level1 等于 level2；但是 level1 等于 level2，is_sufficient_equal 不一定为 True
def is_sufficient_equal(level1: Level, level2: Level) -> bool:
    if level1 is level2:
        return True
    if (
        level1.lower_bound() != level2.lower_bound()
        or level1.upper_bound() != level2.upper_bound()
    ):
        return False
    if isinstance(level1, ParamLevel):
        if isinstance(level2, ParamLevel):
            return level1.name == level2.name
    if isinstance(level1, MVarLevel):
        if isinstance(level2, MVarLevel):
            return level1.name == level2.name
    if isinstance(level1, NatLevel):
        return True  # 开头已经判断过了上下界相等，所以 level1.value == level2.value
    if isinstance(level1, SuccLevel):
        if isinstance(level2, SuccLevel):
            if level1.offset == level2.offset:
                return is_sufficient_equal(level1.level, level2.level)
            elif level1.offset > level2.offset:
                return is_sufficient_equal(
                    SuccLevel(level1.level, level1.offset - level2.offset), level2.level
                )
            else:
                return is_sufficient_equal(
                    level1.level, SuccLevel(level2.level, level2.offset - level1.offset)
                )
    if isinstance(level1, MaxLevel):
        if isinstance(level2, MaxLevel):
            if len(level1.levels) != len(level2.levels):
                return False
            for i in range(len(level1.levels)):
                if not is_sufficient_equal(level1.levels[i], level2.levels[i]):
                    return False
            return True
    if isinstance(level1, IMaxLevel):
        if isinstance(level2, IMaxLevel):
            return is_sufficient_equal(
                level1.left, level2.left
            ) and is_sufficient_equal(level1.right, level2.right)
    return False  # 其他情况默认不相等


def mk_normalize_succ_level(norm_level: Level, offset: int) -> Level:
    if norm_level.is_constant():
        return NatLevel(int(norm_level.lower_bound()) + offset)
    if isinstance(norm_level, SuccLevel):
        return SuccLevel(norm_level.level, norm_level.offset + offset)
    if isinstance(norm_level, MaxLevel):
        return mk_normalize_max_level(
            [mk_normalize_succ_level(level, offset) for level in norm_level.levels]
        )
    return SuccLevel(norm_level, offset)


def mk_normalize_imax_level(norm_left: Level, norm_right: Level) -> Level:
    if norm_right.is_constant() and norm_right.lower_bound() == 0:
        return NatLevel(0)
    if norm_left.is_constant() and norm_left.lower_bound() <= 1:
        return norm_right
    if is_sufficient_equal(norm_left, norm_right):
        return norm_left
    if norm_right.lower_bound() > 0:
        return mk_normalize_max_level([norm_left, norm_right])
    return IMaxLevel(norm_left, norm_right)


def type_code(level: Level) -> int:
    if isinstance(level, NatLevel):
        return 1
    if isinstance(level, SuccLevel):
        return 2
    if isinstance(level, MaxLevel):
        return 3
    if isinstance(level, IMaxLevel):
        return 4
    if isinstance(level, ParamLevel):
        return 5
    if isinstance(level, MVarLevel):
        return 6
    raise Exception("Unsupported level type")


def is_norm_lt(norm_level1: Level, norm_level2: Level) -> int:
    if is_sufficient_equal(norm_level1, norm_level2):
        return 0
    if norm_level1.lower_bound() != norm_level2.lower_bound():
        return int(norm_level1.lower_bound() - norm_level2.lower_bound())
    elif norm_level1.upper_bound() != norm_level2.upper_bound():
        return int(norm_level1.upper_bound() - norm_level2.upper_bound())
    if type_code(norm_level1) != type_code(norm_level2):
        return int(type_code(norm_level1) - type_code(norm_level2))
    if isinstance(norm_level1, ParamLevel) or isinstance(norm_level1, MVarLevel):
        assert isinstance(norm_level2, ParamLevel) or isinstance(
            norm_level2, MVarLevel
        ), "Out of bound 3"
        return (
            -1
            if norm_level1.name < norm_level2.name
            else (1 if norm_level1.name > norm_level2.name else 0)
        )
    if isinstance(norm_level1, SuccLevel):
        assert isinstance(norm_level2, SuccLevel), "Out of bound 4"
        if norm_level1.offset < norm_level2.offset:
            return is_norm_lt(
                norm_level1.level,
                SuccLevel(norm_level2.level, norm_level2.offset - norm_level1.offset),
            )
        elif norm_level1.offset > norm_level2.offset:
            return is_norm_lt(
                SuccLevel(norm_level1.level, norm_level1.offset - norm_level2.offset),
                norm_level2.level,
            )
        return is_norm_lt(norm_level1.level, norm_level2.level)
    elif isinstance(norm_level1, IMaxLevel):
        assert isinstance(norm_level2, IMaxLevel), "Out of bound 5"
        return is_norm_lt(norm_level1.left, norm_level2.left) or is_norm_lt(
            norm_level1.right, norm_level2.right
        )
    elif isinstance(norm_level1, MaxLevel):
        assert isinstance(norm_level2, MaxLevel), "Out of bound 6"
        for i in range(min(len(norm_level1.levels), len(norm_level2.levels))):
            if is_norm_lt(norm_level1.levels[i], norm_level2.levels[i]):
                return True
        return len(norm_level1.levels) < len(norm_level2.levels)
    raise Exception("Unsupported level type")


def mk_normalize_max_level(norm_levels: list[Level]) -> Level:
    if len(norm_levels) == 1:
        return norm_levels[0]
    args: list[Level] = []
    max_lower_bound = max([level.lower_bound() for level in norm_levels])
    for level in norm_levels:
        # 最终的表达式 upper_bound 一定大于 lower_bound，所以不需要考虑小于等于 max_lower_bound 的子项
        if level.upper_bound() <= max_lower_bound:
            continue
        if isinstance(level, MaxLevel):
            for arg in level.levels:
                if len(args) == 0 or any(
                    not is_sufficient_equal(arg, existing_arg) for existing_arg in args
                ):
                    args.append(arg)
        elif len(args) == 0 or any(
            not is_sufficient_equal(level, existing_arg) for existing_arg in args
        ):
            args.append(level)
    if len(args) == 1:
        return args[0]
    # 缺少一个排序
    sorted_args = sorted(args, key=cmp_to_key(lambda a, b: is_norm_lt(a, b)))
    return MaxLevel(sorted_args)


def normalize_level(level: Level) -> Level:
    if level.is_constant():
        return NatLevel(int(level.lower_bound()))
    if (
        isinstance(level, NatLevel)
        or isinstance(level, ParamLevel)
        or isinstance(level, MVarLevel)
    ):
        return level
    if isinstance(level, SuccLevel):
        level, offset = level.level, level.offset
        while isinstance(level, SuccLevel):
            level, offset = level.level, offset + level.offset
        return mk_normalize_succ_level(normalize_level(level), offset)
    if isinstance(level, IMaxLevel):
        left = normalize_level(level.left)
        right = normalize_level(level.right)
        return mk_normalize_imax_level(left, right)
    elif isinstance(level, MaxLevel):
        return mk_normalize_max_level(
            [normalize_level(level) for level in level.levels]
        )
    else:
        raise Exception("Unsupported level type")


def is_equivalent(level1: Level, level2: Level) -> bool:
    if is_sufficient_equal(level1, level2):
        return True
    return is_sufficient_equal(normalize_level(level1), normalize_level(level2))


def is_geq(level1: Level, level2: Level) -> bool:
    return is_geq_core(normalize_level(level1), normalize_level(level2))


def is_geq_core(level1: Level, level2: Level) -> bool:
    if (
        is_sufficient_equal(level1, level2)
        or level1.lower_bound() >= level2.upper_bound()
    ):
        return True
    if isinstance(level2, MaxLevel):
        return all(is_geq_core(level1, arg) for arg in level2.levels)
    if isinstance(level1, MaxLevel):
        return any(is_geq_core(arg, level2) for arg in level1.levels)
    if isinstance(level2, IMaxLevel):
        # level2.left 和 level2.right 已经是 normalized
        return is_geq_core(level1, level2.left) and is_geq_core(level1, level2.right)
    if isinstance(level1, IMaxLevel):
        # level1.right 已经是 normalized
        return is_geq(level1.right, level2)
    if isinstance(level1, SuccLevel):
        if not isinstance(level2, SuccLevel):
            if is_sufficient_equal(level1.level, level2):
                return level1.offset >= 0
        else:
            if level1.offset == level2.offset:
                return is_geq_core(level1.level, level2.level)
            elif level1.offset > level2.offset:
                return is_sufficient_equal(level1.level, level2.level)
    return False
