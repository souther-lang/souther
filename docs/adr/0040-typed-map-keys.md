# ADR-0040: A Map key may be a String-backed newtype, not only String

Status: Accepted. Amended — the restriction is a boundary rule, not a rule about every map, and a
temporal key crosses too (see "Where the restriction applies"). The in-language type and operations
are implemented, and so is the boundary codec: a keyed map may be a data field or behavior I/O,
decoding each string key into the key type (a newtype invariant-checked, a temporal parsed from its
ISO form) and encoding it back bare.

## Context

`Map` was fixed to `Map<String, V>`. A domain map is almost always keyed by an identifier that has a
type — `Map<商品ID, 在庫>`, `Map<従業員ID, 権限>` — and forcing the key to `String` throws that type
away: `商品ID` and `従業員ID` become the same key type, and a caller can pass one where the other is
meant. It also runs against Souther's whole stance of putting distinctions in types (closed
construction, newtypes). Elm's `Dict` and F#'s `Map` both key by a typed value.

The key cannot be an arbitrary type, though. A `Map`'s external representation is a JSON object, whose
keys are strings, so a key type must be renderable as (and parseable from) a bare string. A
String-backed newtype (`data 商品ID = String`) is exactly that: nominally distinct, bare-string
represented (ADR-0014).

## Decision

A `Map` key is `String` or a **String-backed newtype** (`data X = String`) — no other type. `MapOf`
carries both a key and a value type. The key is validated at type resolution: `String`, a newtype
over `String`, or (inside `core` only) a key type variable `'k` that monomorphises to one of those.

- **Runtime.** The map is keyed by the key value itself — a `String`, or the newtype wrapper — and
  java's `Map` compares keys by their value equality (ADR-0009, the equality every data already has),
  so `containsKey(商品ID("P-01"), m)` matches a stored `商品ID("P-01")`. `Map.keys` returns
  `List<商品ID>`, keeping the type.
- **Standard library** generalises over the key: `containsKey` / `insert` / `remove` / `singleton` /
  `get` / `keys` / `toList` / `fromList` take and return the key type. `Map.empty` is the
  empty-collection bottom in both key and value, fixed by context like `[]`.
- **Boundary codec.** A `Map<商品ID, V>` is a JSON object with bare-string keys. Decoding reads the
  object with the value decoder, then runs the key newtype's own decoder on each string key, so the
  key's invariant is enforced and a bad key fails the decode at that key's path (issues accumulate
  across the map). Encoding renders each key `商品ID` back to its bare `value` before writing the
  object. The runtime carries no Raoh dependency (ADR-0004): the key-remap runs in a small helper the
  decoder class generates, and the encode-side stringify is a pure key rewrite in souther-runtime.

## Where the restriction applies

The decision above says "a `Map` key is `String` or a String-backed newtype", and the check ran at
type resolution — so it saw every *written* type and nothing else. `List.groupBy` and `List.indexBy`
build a map keyed by whatever the projection returns, so the compiler produced `Map<Date, V>` values
of a type it refused to let anyone write, and refused even a local annotation naming what `groupBy`
had just returned (issue #100).

That was not unsound — every escape route out of a body is a written type — but the rule as stated was
not the rule enforced. The reason for the restriction is representational, and representation is a
boundary concern: **the key check belongs at the boundary**. A data field and a behavior's input and
output are checked, at any depth; a map that stays inside a body may be keyed by any value.

The boundary set also admits `Date` and `DateTime`. What a key must satisfy is "renderable as, and
parseable from, a bare string", and a temporal already crosses that way — a `Date` field travels as
its ISO 8601 form, so `Map<Date, 金額>` is a JSON object whose keys are the same strings that field
would carry. Daily aggregation, which had no expressible form, is `{"2026-01-01": 300}`.

An `Int`-backed newtype key stays out. It meets the letter of "parseable from a string" but not the
spirit: the same value is a JSON number in a field and would be a string in a key, so the type's
external form would depend on where it appears.

An *enumeration* — a sum every one of whose cases is a unit data — is admitted, and by that same
rule rather than despite it. Such a sum travels as its case's name in every position, a field
included (ADR-0069), so a key is the representation it already has: `{"stage": "Won"}` and
`{"Won": 300}` carry the same string. Its key is decoded by the sum's own decoder, so a name no case
answers to fails at that key's path, as a newtype's invariant does.

## Consequences

`Map<商品ID, 在庫>` and `Map<従業員ID, 権限>` are distinct types, and the key of a lookup is checked
against the map's key type, so the two cannot be confused. Building and querying a keyed map — the
aggregation the review asked for (add/update/remove an entry by a typed key) — works in a behavior
body, and such a map now crosses the boundary too: a behavior can receive or return `Map<商品ID, V>`
directly, and a key that violates the newtype's invariant is a decode failure at that key's path,
not a silently accepted string.

A boundary key stays string-rendered on purpose: admitting an arbitrary value key would need an
entry-array representation (a JSON object cannot key by a non-string), which changes the boundary
format. A String-backed newtype and a temporal both keep the `Map` a plain JSON object — the minimal,
representation-preserving step (the option chosen over a value-key design). Inside a body no format
is at stake, so nothing is restricted there.

## References

- ADR-0069 (what holds of every case is a property of the sum — why an enumeration is a key)
- ADR-0014 (a newtype is nominal and bare-string represented — why a String-backed newtype is a valid
  key)
- ADR-0009 (value equality — how a newtype-keyed map matches keys)
- ADR-0004 (derived codecs, souther-runtime is Raoh-free — the constraint the key codec meets)
- Specification: `[#collections]`, `[#stdlib-map]`
- Prior art: Elm `Dict`, F# `Map` (typed keys)
