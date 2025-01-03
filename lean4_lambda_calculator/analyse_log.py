from collections import defaultdict
import re

def analyze_log(log_file):
    execution_times = defaultdict(list)

    # 正则匹配日志记录的函数名称和耗时（单位为毫秒）
    pattern = re.compile(r"(\w+) executed in ([\d.]+) ms")

    with open(log_file, "r") as f:
        for line in f:
            match = pattern.search(line)
            if match:
                func_name = match.group(1)
                duration_ms = float(match.group(2))
                execution_times[func_name].append(duration_ms)

    # 统计分析
    stats = {}
    for func, times in execution_times.items():
        stats[func] = {
            "count": len(times),
            "min_time": min(times),
            "max_time": max(times),
            "average_time": sum(times) / len(times),
        }

    return stats

if __name__ == "__main__":
    log_file = "execution_times.log"
    stats = analyze_log(log_file)
    for func, data in stats.items():
        print(f"Function: {func}")
        print(f"  Executions: {data['count']}")
        print(f"  Min Time: {data['min_time']:.2f} ms")
        print(f"  Max Time: {data['max_time']:.2f} ms")
        print(f"  Average Time: {data['average_time']:.2f} ms")