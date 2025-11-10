#!/usr/bin/env python3
import re
from pathlib import Path

SRC = Path('vendor/torch.sr')
OUT = Path('vendor/torch_pooled.sr')  # write to a new file

code = SRC.read_text()

# Replace all Tensor literal wrappers with pool-aware helper.
# Pattern: Tensor{ t: <expr> }
pattern = re.compile(r"Tensor\{\s*t:\s*([^}]+?)\s*\}")

def repl(m: re.Match) -> str:
    expr = m.group(1).strip()
    return f"wrap_and_track({expr})"

new_code = pattern.sub(repl, code)

# Optional: ensure wrap_and_track is available by adding a comment marker (no import needed in SR for same package).

if new_code != code:
    OUT.write_text(new_code)
else:
    print('No changes applied; pattern not found or already pool-aware.')

print('Rewrote vendor/torch.sr to use pool-aware wrappers.')
