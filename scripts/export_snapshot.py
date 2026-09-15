#!/usr/bin/env python3
"""Export repository text for an atomic GitHub tree checkpoint.

This local script does not access credentials or contact GitHub.
PDFs and compiled files are excluded from the text manifest.
"""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
suffixes = {'.py', '.cpp', '.c', '.lean', '.toml', '.json', '.txt', '.md',
            '.yaml', '.yml', '.tex', '.ipynb', '.sh'}
names = {'LICENSE', '.gitignore', 'lean-toolchain', 'Makefile'}
skip = {'.git', '.lake', '__pycache__', 'build'}
files = []
for path in sorted(root.rglob('*')):
    if not path.is_file() or any(part in skip for part in path.relative_to(root).parts):
        continue
    if path.suffix in suffixes or path.name in names:
        files.append({'path': path.relative_to(root).as_posix(),
                      'mode': '100644', 'type': 'blob',
                      'content': path.read_text(encoding='utf-8')})
print(json.dumps(files))
