from setuptools import setup, find_packages

setup(
    name="lean4_lambda_calculator",
    version="0.1.0",
    author="PengLingwei",
    author_email="penglingwei1996@qq.com",
    description="A lambda calculator implemented in Lean4",
    long_description=open("README.md").read(),
    long_description_content_type="text/markdown",
    url="https://github.com/yourusername/lean4_lambda_calculator",
    packages=find_packages(),
    install_requires=[
        "colorama",
        "prompt_toolkit",
    ],
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.6',
)
