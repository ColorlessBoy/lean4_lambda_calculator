import json
import subprocess
import time

# 启动 Lean 4 LSP 服务器
def start_lean_lsp():
    # 启动 Lean 4 LSP 进程
    process = subprocess.Popen(
        ['lean', '--server'],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE
    )
    return process

# 发送请求并获取响应
def send_request(process, message):
    # 发送消息给 Lean 4 LSP
    process.stdin.write((json.dumps(message) + '\n').encode('utf-8'))
    process.stdin.flush()

    # 等待并读取响应
    time.sleep(1)  # 等待 LSP 服务器响应
    response = process.stdout.readline().decode('utf-8')
    
    # 打印响应进行调试
    print("LSP Response:", response)

    # 如果没有响应，返回空字典
    if not response:
        # 捕获错误输出
        error_output = process.stderr.read().decode('utf-8')
        print("LSP Error Output:", error_output)
        raise ValueError("No response from Lean 4 LSP")

    return json.loads(response)

# 处理报错信息
def process_errors(errors):
    for error in errors:
        if "consider marking it as 'noncomputable'" in error:
            print(f"Noncomputable suggestion found: {error}")

def main():
    # 启动 Lean 4 LSP 服务器
    process = start_lean_lsp()

    # 给 LSP 发送初始化请求
    init_message = {
        "jsonrpc": "2.0",
        "method": "initialize",
        "params": {
            "processId": 12345,
            "rootUri": "file:///Users/penglingwei/Documents/prover/lean/lean4_lambda_calculator",
            "capabilities": {}
        },
        "id": 1
    }

    # 发送初始化请求
    response = send_request(process, init_message)
    print("Initialization response:", response)

    # 发送文件打开请求
    open_message = {
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": "file:///Users/penglingwei/Documents/prover/lean/lean4_lambda_calculator/query_const.lean",
                "languageId": "lean",
                "version": 1,
                "text": "your Lean 4 code here"
            }
        }
    }
    send_request(process, open_message)

    # 发送诊断请求来获取编译错误
    diag_message = {
        "jsonrpc": "2.0",
        "method": "textDocument/publishDiagnostics",
        "params": {
            "uri": "file:///Users/penglingwei/Documents/prover/lean/lean4_lambda_calculator/query_const.lean",
            "diagnostics": [
                {
                    "severity": 1,
                    "message": "failed to compile definition, consider marking it as 'noncomputable' because it depends on ...",
                    "source": "Lean",
                    "code": "noncomputable"
                }
            ]
        }
    }
    
    # 处理并提取错误信息
    send_request(process, diag_message)
    process_errors([diag_message['params']['diagnostics'][0]['message']])

if __name__ == "__main__":
    main()