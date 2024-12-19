from huggingface_hub import hf_hub_download, list_repo_files
import os
import sys
import re
from pathlib import Path
from zipfile import ZipFile
from tqdm import tqdm
import shutil

repo_id = "colorlessboy/mathlib4-thms"

BASE_FOLDER = "data"

def download_zip_file(filename: str): 
    extract_path = os.path.join(BASE_FOLDER, Path(filename).stem)
    # 检查 extract_path 是否非空
    if os.path.exists(extract_path) and any(os.scandir(extract_path)):
        print(f"{extract_path} 已存在且非空，跳过下载和解压。")
        return extract_path
    repo_id = "colorlessboy/mathlib4-thms"
    filepath = hf_hub_download(repo_id=repo_id, repo_type="dataset", filename=filename)
    with ZipFile(filepath, 'r') as zip_ref:
        zip_ref.extractall(extract_path)
    print(f"成功下载{filename}")
    return extract_path

def get_huggingface_zip(filename: str | None = None):
    # 获取文件名列表
    file_names = list_repo_files(repo_id=repo_id, repo_type="dataset")
    # 正则表达式匹配模式
    if filename is not None:
        pattern = filename + r"-\d+-\d+\.zip"
    else: 
        pattern = r"thm\w+-\d+-\d+\.zip"
    # 用于存放解析后的结果
    zippaths = []
    for file_name in file_names:
        if re.match(pattern, file_name):
            zippath = download_zip_file(file_name)
            zippaths.append(zippath)
    return zippaths

def join_folders(source_folders: list[str], target_folder: str):
    if os.path.exists(target_folder):
        print(f"{target_folder} is exists.")
        return
    os.mkdir(target_folder)
    for source_folder in tqdm(source_folders):
        for file_name in tqdm(os.listdir(source_folder)):
            source_file = os.path.join(source_folder, file_name)
            try:
                shutil.move(source_file, target_folder)
            except Exception as e:
                print(e)

if __name__ == "__main__":
    from dotenv import load_dotenv
    load_dotenv()
    filename = sys.argv[1] if len(sys.argv) > 1 else None

    target_folder = os.path.join('data', 'thms')
    if not os.path.exists(target_folder):
        zippaths = get_huggingface_zip(filename)
        join_folders(source_folders=zippaths, target_folder=target_folder)
        for zippath in zippaths:
            shutil.rmtree(zippath)

    target_file = os.path.join('data', 'thms.txt')
    with open(target_file, 'w') as f:
        for thm in tqdm(os.listdir(target_folder)):
            name = Path(thm).stem
            f.write(f"{name}\n")
