from typing import TypeVar, Generic, List

T = TypeVar('T')  # 定义一个类型变量 T

class Context(Generic[T]):
    def __init__(self):
        self.data: List[T] = []  # 使用泛型类型 T
    
    def push(self, arg: T) -> None:
        self.data.append(arg)
    
    def pop(self) -> T:
        return self.data.pop()

    def __len__(self) -> int:
        return len(self.data)
    
    def __reversed_index__(self, index: int) ->int:
        return self.__len__() - index - 1

    def __getitem__(self, index: int) -> T:
        if 0 <= index < len(self.data):
            return self.data[self.__reversed_index__(index)]
        else:
            raise IndexError("Index out of range")

    def __setitem__(self, index: int, value: T) -> None:
        if 0 <= index < len(self.data):
            self.data[self.__reversed_index__(index)] = value
        else:
            raise IndexError("Index out of range")
    
    def __add__(self, other: 'Context[T]') -> 'Context[T]':
        new_context = Context[T]()
        new_context.data = self.data + other.data
        return new_context

    def __iter__(self):
        return reversed(self.data)
    
    def __repr__(self):
        return self.data[::-1].__repr__()