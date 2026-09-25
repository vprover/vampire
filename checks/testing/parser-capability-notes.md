# Parser capability contracts

Some valid standard syntax is currently rejected by Vampire. A passing
rejection contract confirms the diagnostic; it does not establish language
conformance or a successful semantic result.

Two arithmetic examples are `$abs(1.0)=1.0` and `$quotient(1,2)=1/2`.
Both are well-typed, satisfiable formulas under the standard arithmetic
interpretation, but the corresponding cases expect Vampire's current
unsupported-operation diagnostic. See the
[TPTP arithmetic specification](https://tptp.org/UserDocs/TPTPLanguage/ArithmeticSystem.html).

Run them from a prepared build using a fresh result directory:

```sh
python3 checks/testing/run.py run --build build/testing/debug --suite parsers \
  --filter '^parser/reject-tptp/(quotient-integer|abs-real)$' \
  --output build/testing/results/parser-capabilities
```

Other rejection cases specify their expected error. A crash, assertion or an
unrelated early type error does not satisfy that contract. Semantic, capability
and malformed-input tests keep distinct descriptions.
