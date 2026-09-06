# Problem 406 Bridge Layer

The bridge layer is the reviewer path from the GST structural engine to the comparator theorem.

## Chain of responsibility

```text
GST structural engine
  -> CommonTwo / HappyCell / CreationCertificate
  -> digit two in powers of four
  -> digit two in powers of two
  -> Problem 406 endpoint
```

## Lean-facing shape

The bridge is represented by small public modules, not by rewriting the monolith:

- `GST/Arithmetic/TernaryDigits.lean` exposes ternary digit vocabulary.
- `GST/Arithmetic/Carries.lean` exposes carry vocabulary.
- `GST/FourPower/CommonTwo.lean` exposes common-two witnesses.
- `GST/FourPower/PrefixLaw.lean` exposes exponent-prefix vocabulary.
- `GST/FourPower/Certificate.lean` exposes the certificate-to-navigation bridge.
- `GST/Problem406/PublicAPI.lean` exposes the final clean Problem 406 theorem.

## Reviewer promise

A reviewer should be able to inspect the public theorem first, then walk backwards through wrapper modules and theorem maps until reaching the protected proof checkpoint. The wrapper layer must not invent new mathematics; it only gives stable names to already-proved declarations.
