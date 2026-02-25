# Lean4 Lambda Calculator

This project is now managed with **uv** and uses **ruff** for linting.

## Development setup

1. Install [uv](https://docs.astral.sh/uv/getting-started/installation/) if you haven't already:
   ```bash
   curl -LsSf https://astral.sh/uv/install.sh | sh
   ```
   or `pip install uv`.

2. Create and sync the virtual environment:
   ```bash
   uv sync  # reads pyproject.toml and installs dependencies
   ```

3. Run the tests:
   ```bash
   uv run pytest
   ```

4. Lint the code with ruff:
   ```bash
   uv run ruff check .
   ```

## Usage

```bash
python lean4_lambda_calculator/shell.py
```

```bash
lake env lean --run QueryConst.lean <ConstName>
```