from pathlib import Path


def normalize_chronology_header(text: str) -> str:
    lines = text.splitlines(keepends=True)
    end = None
    for i, line in enumerate(lines[:100]):
        if line.strip() == '/- ====================================================================== -/':
            end = i
            break
    if end is None:
        return text
    for i in range(end + 1):
        if lines[i].startswith('/-'):
            lines[i] = '--' + lines[i][2:]
    return ''.join(lines)

# Canonical proof body: syntax-only chronology repair. Do not alter any theorem.
proof = Path('ErdosTernary2.lean')
proof_text = proof.read_text(encoding='utf-8')
proof.write_text(normalize_chronology_header(proof_text), encoding='utf-8')

# Reconstruct the shared tactic module shipped with the imported workspace.
support_src = Path('ker07-snapshot/GSTTactic.lean')
support_dst = Path('GSTTactic.lean')
support_text = normalize_chronology_header(support_src.read_text(encoding='utf-8'))
support_dst.write_text(support_text, encoding='utf-8')
