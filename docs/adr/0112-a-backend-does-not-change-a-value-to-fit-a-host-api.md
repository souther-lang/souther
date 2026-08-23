# ADR-0112: A backend does not change a value to fit a host API

Status: Accepted.

## Context

`Decimal.divide(a, b, scale, mode)` takes its scale as an `Int`, which is signed 64-bit, and
`BigDecimal.divide` takes a JVM `int`. The backend put the one into the other with a raw `l2i`
(issue #976). A scale of `4294967298` divided at scale 2: nothing aborted and nothing was reported,
which is the shape `[#stdlib-int]` refuses everywhere else — an `Int` operation that leaves the
range it holds aborts rather than wrapping. `Decimal.round` did the same with a `(int)` cast in the
runtime.

Two more things came out of reading around it, and they decide the shape of the answer rather than
adding to a list of sites.

The first is that narrowing is not the whole failure. A scale of `2147483647` *is* handed over
exactly, and `BigDecimal` still refuses the division ("BigInteger would overflow supported range").
So does `add`, `subtract` and `multiply` at the ends of the scale range. Those reached a Souther
boundary as `java.lang.ArithmeticException` — a `java.math` type named in the failure of a program
that has no such type — and `p.a * p.a` on a decoded value was enough to get one. Holding the scale
to an `int` would have left every one of those open.

The second is that the check had already worked around the backend's silence. `placesOf` refused to
state a range for a scale no `int` holds, and `[#invariant-discharge-arithmetic]` wrote down the
reason: what the backend divides at is that scale narrowed, so a proof over the number as written
would be a proof about a different division. A rule in the specification was shaped by an
instruction the backend happened to select.

Underneath all three is one thing: no rule said who owns the meeting between a Souther value and a
host API. Elsewhere in the tree the meeting is decided at the meeting point — `Lists.get` tests the
index and answers `None`, `Strings.offsetOf` tests it and aborts, `Temporals.fromDateParts` uses
`Math.toIntExact` and answers `NotADate`, `IntMath` wraps every `Math.*Exact` — but each of those is
a local decision by whoever wrote the site, and nothing made the next site take one.

## Decision

**A backend never changes a Souther value to make it fit a host API.**

Where a host operation has a narrower value domain, a different representation, or failure modes
that are not Souther values, the call is mediated by a runtime kernel that owns that operation.
Representation conversion is exact. Failure is translated to the result or the abort that operation
specifies.

A direct JDK intrinsic (`Intrinsics.JdkVirtual`) is allowed only where passing the value requires no
semantic conversion and the JDK operation answers on every Souther value admitted there.

The line is between knowing a representation and owning a meaning. The backend may know that a
`Decimal` is a `BigDecimal` — it builds a literal, names the type in a descriptor, casts to it. What
it may not do is implement a Souther operation with a `BigDecimal` method: `+` emits a call to
`DecimalMath.add`, not to `BigDecimal.add`. `Int`'s operators already read this way through
`IntMath`; `Decimal`'s did not.

Applied to Decimal, this settles four things.

- Every `decimal.*` kernel is one emitter, `DeclaredStatic` reading the declaration, owned by
  `DecimalMath`. `divide` was written out by hand in `BodyGen`; `add`/`subtract`/`multiply` went
  straight to `BigDecimal`; `compare`/`fromInt` derived a descriptor from the call. One shape now,
  so a Decimal operation added later has one place to be written.
- The four operators emit calls to the same runtime.
- Narrowing a scale and failing an operation are separate, and say so separately. The first is
  exact-or-abort (`Math.toIntExact`); the second catches what `BigDecimal` refuses. A message
  calling the second a scale out of range would be wrong about a scale that was handed over exactly.
- The specification states what the run time takes, and the compiler and the runtime implement it
  separately. The analysis does not call the runtime: a reading whose soundness depended on which
  backend was linked would be a reading that is not about the language. The two are held together by
  a test over the ends of the range.

`JdkVirtual.l2iArgs` is deleted. It had no entries and what it offered was the raw narrowing, in the
one place a later kernel taking a host `int` would have reached for it.

## Consequences

- Decimal arithmetic that runs off the end of the scale range aborts with `ConstraintViolation`
  where it used to throw `java.lang.ArithmeticException` out of a behavior. This is a fix under
  `[#jvm-abort]`, not a new failure: those calls already failed.
- `Decimal.divide` evaluates all four arguments. The hand-written emitter skipped the scale and the
  mode on the zero-divisor branch, which was a short-circuit no declaration wrote down — only `&&`
  and `||` decide which of their operands run (`[#a-condition-stops-when-its-answer-is-settled]`).
  Which of the two invalid conditions decides the answer is a separate question, and is stated:
  a zero divisor answers `DivisionByZero` whatever the scale.
- An abort message over an extreme `Decimal` describes the value by sign, precision and scale rather
  than by `toPlainString()`. Spelling out a value at the far end of the scale range asks for the
  allocation the operation just refused to make, which would have made the failure path fail.
- ADR-0053's compiler-integrated list no longer covers `Decimal.divide` under either of its reasons.
  The primitive-headed-union reason it recorded was already lifted by ADR-0081, and the
  rounding-mode reason it added later — that a mode is a bare identifier no parameter type can name
  — was lifted by ADR-0087, which declares `data RoundingMode` in a core module. `Int.divide` and
  `Int.truncatingRemainder` stay written out in `BodyGen`: their zero divisor is a case the language
  defines, not a host partiality, so they are not what this ADR is about.
- `String.trim`/`lowercase`/`uppercase`/`contains`/`startsWith`/`endsWith`/`append` and
  `DateTime.toDate`/`toTime`/`fromDateAndTime` stay on `JdkVirtual`: the values go over unchanged
  and the operations answer on all of them.
- The rule reaches past this issue by construction — a code point against a UTF-16 offset, a
  temporal range, a size or a count narrowed to a host `int`. Each is the same meeting, and the
  answer at each is the operation's to state.

## References
- Issue #976
- Specification: `[#stdlib-decimal]`, `[#a-scale-is-used-as-the-number-written]`,
  `[#a-division-that-does-not-run-needs-no-scale]`, `[#invariant-discharge-arithmetic]`,
  `[#jvm-abort]`, `[#primitives]`
- ADR-0053 (standard-library implementation-location policy — the exception this closes)
- ADR-0081 (a primitive is a union member a declaration may name)
- ADR-0087 (a rounding mode is an ordinary value of a core-declared data)
