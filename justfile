# Animaker 动画魅客

default:
    @just --list

# 安装依赖
install:
    uv sync

# 安装开发依赖
install-dev:
    uv sync --dev

# 运行 Animaker（GUI）
run:
    uv run animaker

# 运行测试（若有）
test:
    uv run pytest

# 格式化代码
format:
    uv run black .
    uv run ruff format .

# 代码检查
check:
    uv run ruff check .
    uv run mypy .

# 修复代码问题
fix:
    uv run ruff check --fix .
    uv run black .

# 清理缓存
clean:
    rm -rf .pytest_cache
    rm -rf .mypy_cache
    rm -rf .ruff_cache
    find . -type d -name __pycache__ -exec rm -r {} +
    find . -type f -name "*.pyc" -delete

