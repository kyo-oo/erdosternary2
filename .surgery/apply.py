from pathlib import Path

ROOT = Path("ErdosTernary2.lean")
LAKE = Path("lakefile.toml")

s = ROOT.read_text(encoding="utf-8")
original = s

# Remove the known-red production imports.
s = s.replace("import GSTStep6Close\n", "")
s = s.replace("import GSTInfiniteFourPowerNavigation\n", "")

# Collapse repeated import churn while preserving the first import occurrence.
seen = set()
out = []
for line in s.splitlines(keepends=True):
    stripped = line.strip()
    if stripped.startswith("import "):
        module = stripped[len("import "):].strip()
        if module in seen:
            continue
        seen.add(module)
    out.append(line)
s = "".join(out)

old_master = '''theorem gst_four_power_creation_master_inline :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  intro K hK5 hK7
  exact GSTInfiniteFourPowerNavigation.gst_four_power_navigation_universal
    K hK5 hK7
'''
new_master = '''theorem gst_four_power_creation_master_inline :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  intro K hK5 hK7
  simpa [GSTFourPowerOntologicalAdapter.CreationCertificate] using
    (gst_four_power_creation_certificate_inline K hK5 hK7)
'''
if old_master in s:
    s = s.replace(old_master, new_master, 1)
elif new_master not in s:
    raise SystemExit("MASTER_SEAM_NOT_FOUND")

start_marker = "theorem gst_power_two_wave_large\n"
end_marker = "\n/-- The weaker two-wave theorem closes the even exponent directly. -/"
replacement = '''theorem gst_power_two_wave_large
    (a : Nat) (ha : 500 < a) : GSTPowerTwoWave a := by
  unfold GSTPowerTwoWave
  have hnav0 : GSTCanonicalTailStateIso.Navigation (4^a) :=
    GSTFourPowerOntologicalAdapter.gst_four_power_ontological_navigation_of_master
      gst_four_power_creation_master_inline a (by omega) (by omega)
  have hnav : GSTNavigationWitness (4^a) :=
    gst_navigation_witness_of_standalone_navigation (4^a) hnav0
  obtain ⟨p, hd, _hspace⟩ := hnav
  exact Or.inl (hasTernaryTwo_of_digit (4^a) p hd)
'''
if start_marker in s:
    start = s.index(start_marker)
    end = s.index(end_marker, start)
    if s[start:end] != replacement:
        s = s[:start] + replacement + s[end:]
elif replacement not in s:
    raise SystemExit("POWER_TWO_WAVE_SEAM_NOT_FOUND")

ROOT.write_text(s, encoding="utf-8")

t = LAKE.read_text(encoding="utf-8")
t = t.replace('  "GSTInfiniteFourPowerNavigation",\n', "")
t = t.replace('  "GSTStep6Close",\n', "")
LAKE.write_text(t, encoding="utf-8")

for forbidden in (
    "GSTStep6Close",
    "GSTInfiniteFourPowerNavigation",
    "gst_step6_close",
    "information_bad_descends",
):
    if forbidden in s:
        raise SystemExit(f"FORBIDDEN_PRODUCTION_REFERENCE:{forbidden}")

print(f"MONOLITH_CHANGED={int(s != original)}")
print("OBSOLETE_ROUTE_EXCISED=1")
