# ADR-0131: A decoder is Souther's own, and a decoder binding adapts what it reads and how it reports

Status: Accepted. Supersedes the parts of ADR-0004 that name Raoh: that decoders and encoders are
derived from a data's shape and never written in Souther stands.

## Context

ADR-0004 made Raoh the boundary library and emitted Raoh's combinators as the bytecode of every
derived decoder. Three things followed that no model asked for.

- A generated data class names Raoh in the return types of `decoder()` and `encoder()`, and the
  verifier loads those types when it checks the class. A program that only runs behaviors and
  never decodes still fails with `NoClassDefFoundError` without Raoh on the class path.
- What a refusal is called — `too_short`, `out_of_range`, `invariant_violation` — was Raoh's
  vocabulary written into the specification, so an application working in another decoder library
  could not use the derived decoders without changing the language.
- Every module's decoders call the decoders of the modules it imports, so the library is a
  property of a whole program.

Meanwhile almost everything a decode decides was already Souther's: which representation is
admitted as a scalar is answered by souther-runtime; a pattern is run as the machine the class
holds; a clause a constraint states exactly is the checker's claim; a clause no constraint states
runs as a predicate of the class. Raoh contributed the dispatch, the accumulation, the container
of the failures and their names.

## Decision

The derived Decoder is Souther's own, as the derived Encoder is. Both are generated against
souther-runtime's boundary types, and neither names a decoder library.

- A decoder reads its input through a *reader* (`TreeReader`): what a node is, an object's members,
  an array's elements, a scalar's value. souther-runtime has the reader of maps, lists and the
  JDK's values; a reader of another tree belongs to whoever has that tree. What is admitted is
  decided by the decoder, never by a reader.
- A decode answers `Result<T, Refusals>`, the `Result` `__construct` already answers with. Why a
  value is refused is one of seven — absent, not of its kind, not one of the names, not in its
  form, one key twice, a constraint, a clause — each carrying its data, and `Refusal` is sealed over them. A clause
  carries the `InvariantFailure` `__construct` answers with for the same value. A message is not
  part of a refusal: `souther run` says one in Souther's own messages.
- A *decoder binding* adapts a decoder library to the derived decoders: readers of the library's
  trees, the refusals reported in the library's vocabulary, and a derived decoder presented as a
  decoder of the library so that a custom codec written in the library composes with it. It
  decides nothing. A program may use one, several or none.
- Souther ships the Raoh decoder binding, `souther-raoh`, which reports the seven reasons under the
  codes, message keys and metadata the specification used to name, so a resolver keyed on Raoh
  keeps working. A decoder binding for another library depends on souther-runtime and that library
  alone, and may be maintained anywhere.
- A refusal of a constraint carries the constraint's name and data as plain values, so a decoder
  binding written before a constraint was added still reports it.

## Alternatives

- **A codec backend per library in the compiler (`--codec <library>`).** A second copy of the
  decoder bytecode generator per library, and the choice still has to be the same for every module
  of a program, so it would have to be recorded with the linkage and checked.
- **Keep Raoh, and only let a class load without it.** Fixes the first point of the context and
  neither of the others.

## Consequences

`decoder()` and `encoder()` keep their names and their place, and change their types to
souther-runtime's. `jsonDecoder()` and `recordDecoder()` leave the generated API: one decoder reads
every source through its reader. A jOOQ `Record` is read by the Raoh decoder binding as an object
of its columns, so the flat-shape rule that decided whether `recordDecoder()` was generated becomes
a refusal of a field a column cannot hold. A generated class and souther-runtime load without a
decoder library.

The specification states the seven refusals, what each carries and which clauses are constraints,
and the Raoh codes move into the section on the Raoh decoder binding as the translation it
performs. The decoder bytecode generator emits calls into souther-runtime instead of into Raoh;
the existing Raoh decoders are the oracle the derived decoders, seen through the Raoh decoder
binding, are held to until they are removed. `souther run` and the examples read and report with
the derived decoders and Souther's messages, and `souther init` no longer writes Raoh into a build.

A decoder binding that parses text is a reader in the specification's sense, and is held to what it
asks of readers: a member written twice is refused, and a fraction is not rounded to a binary
number before the decoder sees it.

## References

- Specification: `[#external-representation]`, `[#decoder-role]`, `[#custom-codec]`,
  `[#decoder-error]`, `[#what-a-refusal-says]`, `[#what-an-invariant-refusal-says]`,
  `[#codec-generation]`, `[#decoder-binding]`, `[#raoh-binding]`, `[#jvm-codec]`, `[#non-functional]`
- ADR-0004
