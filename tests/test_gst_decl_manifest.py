from pathlib import Path
import sys
import textwrap

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from scripts.gst_decl_manifest import classify_path, extract_declarations


def test_extracts_documented_public_declarations():
    source = textwrap.dedent(
        r'''
        /-- Ternary digit at position p. -/
        def digit3 (N p : Nat) : Nat := (N / 3^p) % 3

        /-- Exact row-two classifier. -/
        theorem row_two_overlap_iff_mod9_five_or_six (K : Nat) : True := by
          trivial
        '''
    )

    decls = extract_declarations("GSTFourPowerDirectResidue.lean", source)

    assert [d.name for d in decls] == [
        "digit3",
        "row_two_overlap_iff_mod9_five_or_six",
    ]
    assert decls[0].kind == "def"
    assert decls[0].doc == "Ternary digit at position p."
    assert decls[1].kind == "theorem"
    assert decls[1].doc == "Exact row-two classifier."


def test_extracts_attributes_and_private_declarations():
    source = textwrap.dedent(
        r'''
        private theorem prefix_mod_exact (b P tail : Nat) : True := by
          trivial

        @[simp] theorem digit3_zero_source (x : Nat) : True := by
          trivial

        noncomputable abbrev Sheet := Nat → Nat → Nat
        structure Cell where
          sourceEnergy : Nat
        inductive Direction
          | horizontalX4
        axiom direct_boundary : True
        '''
    )

    decls = extract_declarations("GSTGraphV2Production.lean", source)

    assert [(d.kind, d.name, d.visibility) for d in decls] == [
        ("theorem", "prefix_mod_exact", "private"),
        ("theorem", "digit3_zero_source", "public"),
        ("abbrev", "Sheet", "public"),
        ("structure", "Cell", "public"),
        ("inductive", "Direction", "public"),
        ("axiom", "direct_boundary", "public"),
    ]


def test_classifies_major_theorem_families():
    assert classify_path("GSTCanonicalTailStateIso.lean") == "Arithmetic core"
    assert classify_path("GSTFourPowerDirectResidue81.lean") == "Four-power direct arithmetic"
    assert classify_path("GSTFourPowerAffineChannelAutomaton.lean") == "Affine channel automaton"
    assert classify_path("GSTGraphV2Production.lean") == "GST Graph V2"
    assert classify_path("GSTU2DSharpCrossingBlock.lean") == "U2D and crossing charge"
    assert classify_path("GST/Problem406/PublicAPI.lean") == "Problem 406 certificate"


def main():
    test_extracts_documented_public_declarations()
    test_extracts_attributes_and_private_declarations()
    test_classifies_major_theorem_families()
    print("GST_DECL_MANIFEST_TESTS_PASS=1")


if __name__ == "__main__":
    main()
