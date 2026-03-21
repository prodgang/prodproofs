#!/usr/bin/env python3
"""Find lemmas/theorems defined in Prod/*.lean that are never referenced elsewhere."""

import re
from pathlib import Path

LEAN_DIR = Path(__file__).parent / "Prod"
DECL_KEYWORDS = {"lemma", "theorem", "def", "abbrev"}

def extract_declarations(text):
    """Extract (name, qualified_name) for all named declarations, tracking namespace."""
    decls = []
    namespace_stack = []

    for line in text.splitlines():
        # Track namespace open/close
        ns_open = re.match(r'^\s*namespace\s+(\S+)', line)
        if ns_open:
            namespace_stack.append(ns_open.group(1))
            continue

        end_match = re.match(r'^\s*end\s+(\S+)', line)
        if end_match and namespace_stack and namespace_stack[-1] == end_match.group(1):
            namespace_stack.pop()
            continue

        # Match declarations
        decl_match = re.match(
            r'^\s*(?:@\[.*?\]\s*)*(?:private\s+|protected\s+)?(?:'
            + '|'.join(DECL_KEYWORDS) + r')\s+(\w+)',
            line
        )
        if decl_match:
            name = decl_match.group(1)
            qualified = '.'.join(namespace_stack + [name]) if namespace_stack else name
            decls.append((name, qualified))

    return decls

def main():
    files = sorted(LEAN_DIR.glob("*.lean"))

    # Collect all declarations with their source file and qualified name
    all_decls = {}  # qualified_name -> (short_name, filename)
    file_texts = {}

    for f in files:
        text = f.read_text()
        file_texts[f.name] = text
        for name, qualified in extract_declarations(text):
            if qualified in all_decls:
                prev = all_decls[qualified][1]
                if prev != f.name:
                    print(f"  [warn] duplicate '{qualified}' in {f.name} and {prev}")
            all_decls[qualified] = (name, f.name)

    combined = "\n".join(file_texts.values())

    unused = []
    for qualified, (name, source_file) in sorted(all_decls.items()):
        # Count occurrences of the short name (word-boundary — catches Namespace.foo usage too)
        matches = len(re.findall(rf'\b{re.escape(name)}\b', combined))
        # Definition line counts as 1; anything beyond is actual usage
        if matches <= 1:
            unused.append((qualified, source_file))

    print(f"\nScanned {len(files)} files, {len(all_decls)} declarations total.\n")
    if unused:
        print(f"Potentially unused ({len(unused)}):")
        current_file = None
        for qualified, source_file in sorted(unused, key=lambda x: (x[1], x[0])):
            if source_file != current_file:
                print(f"\n  [{source_file}]")
                current_file = source_file
            print(f"    {qualified}")
    else:
        print("No unused declarations found.")

if __name__ == "__main__":
    main()
