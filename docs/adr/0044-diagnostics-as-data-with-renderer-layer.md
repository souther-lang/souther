# ADR-0044: Diagnostics are data rendered by a locale-aware layer

Status: Accepted. Revised 2026-08-07 — see *Revision*.

## Revision (2026-08-07)

The original Decision resolved the locale as `--lang` > `SOUTHER_LANG` > the JVM default > Japanese.
The last two steps are withdrawn: the chain is now `--lang` > `SOUTHER_LANG` > English, and the JVM
default locale is not read at all. `Messages.defaultLocale()` answers English and is the one place
the default is written.

Everything the toolchain ships to be read is in English — `specification.adoc`, every bundled
library topic, the CLI's own topics — so a reader on a Japanese desktop who passed no flag was
answered out of `messages_ja.properties` while every document that would explain the answer was in
the other language. The JVM default is what made this depend on where the compiler ran: it says
which language the machine's interface is in, which for a toolchain documented in one language
cannot be evidence about the reader, because most values of it select an answer with nothing behind
it to read.

The rule this leaves is about the default and only the default: when nothing names a language, a
diagnostic is answered in the language the shipped documentation is written in. Naming one is a
different act, and there are three sources of a language, not one.

- Nothing names one — English, because that is the language the shipped core documentation is
  written in.
- Something names one: `--lang`, `SOUTHER_LANG`, or an adapter's own option — that language,
  whether or not documentation exists in it.
- The machine's locale — never, at any entry point.

`SOUTHER_LANG` belongs to the second and not the third. It is Souther's own variable, not `LANG`:
nothing has a value for it until somebody writes one, so a session answered in French is a session
that was configured for French. What the JVM default supplied was a language nobody chose, which is
the whole of what was withdrawn.

So `messages_ja.properties` stays and `--lang ja` still answers out of it. What ships in Japanese is
diagnostic rendering; the language of the documentation is the reason English is the default, and
not a ceiling on which languages may be rendered. The two need not move together because the code
holds them apart: `E2011` is the same string in every language, and `souther doc e2011` answers out
of the specification in English, so a reader answered in a language the documents are not written in
still has the way back. Requiring the catalogs to offer only languages the documentation is written
in would be a policy about what may be translated first, and nothing here argues for one. Readers
who were being served Japanese by default keep it with `SOUTHER_LANG=ja` in a shell profile.

What does bind is each catalog on its own: every catalog that ships defines the base's complete key
set, and is valid on its own terms — no duplicate key, every message a well-formed `MessageFormat`
pattern, every standard-library name it quotes one the library publishes. The build discovers the
catalogs from the tree rather than naming them, so a catalog added tomorrow is under all of it, and
one language has one catalog: two files naming it are two answers to one lookup, settled by class
path order.

Every message is a pattern, and is rendered as one whether or not the site passed anything to put
in it. `Messages.get` used to return a message that took no arguments as written, which left the
catalog's own text meaning two things: a message that quoted a brace so it would survive formatting
was shown to the reader with the quotes still in it, and a message that did not quote one was a
pattern nobody could format — the second of which throws the moment somebody gives that diagnostic
an argument. Neither is visible in the message. So a literal brace is written `'{'` and a literal
apostrophe `''`, in every message, and the build refuses a catalog the formatter cannot read. The
formatter refusing at run time is answered with the text as written, for the same reason a missing
key renders as itself: a compiler reporting an error is the worst place to raise another one.

That narrows what the fallback is for. It was the migration mechanism — a message became Japanese as
it was migrated and read English until then, and a catalog was allowed to ship half-written. It is
now a fail-safe: `ResourceBundle` still answers from the base for a key a locale is missing, and a
key missing everywhere still renders as itself rather than stopping a compile, but no catalog that
ships may depend on either. An incomplete catalog does not fail where anyone can see it; it answers
one diagnostic half in each language, the title and the hint from the base and the message from the
catalog, which is what a third catalog of three keys was found doing.

Amending in place rather than superseding: what changed is a default, the reason for it, and what a
catalog has to be to ship — not the shape of the decision. Diagnostics are still data rendered by a
locale-aware layer, and the code
and type strings are still locale-independent, which is what makes a code a lookup that survives
being answered in a language the reader does not read. Two surfaces still name a language of their
own and are untouched here: the LSP renders in English because a language server is not told the
editor's UI locale, and the annotation processor resolves from `souther.lang`. That the policy is
written in each adapter rather than in one place is a separate problem from which language it names.

## Context

Souther grounds its syntax in Elm, and Elm's error messages are a large part of why people reach for
it: a titled report, the offending source line quoted with a caret under the problem, the two types
that disagree shown side by side, and a hint on how to fix it. Souther's compile errors did not come
close. A single `CompileException` carried a `SourcePos` and an optional code, and its message was
built by string concatenation at the throw site and frozen into the exception at construction. The
CLI printed `e.getMessage()` verbatim — one line of `line:col CODE: message`, no source snippet, no
caret, no color. About 180 throw sites each spelled their message inline in English; only ~15 codes
were wired. There was no message catalog and no locale: the text was English, always.

Three things were wanted, and they turned out to share one prerequisite.

- Elm-quality human output — a snippet, a caret, found-vs-expected type blocks, hints.
- Machine-readable output for tools and agents — a stable code and source region a program can act
  on without parsing prose. (JSON is not "more readable" to a model; its value is a stable identity
  and coordinates that do not move when the prose or the locale changes.)
- Japanese and English messages. The author, the book (smdd-book), and the expected audience are
  Japanese; English is the second locale.

The shared prerequisite is to stop freezing a formatted string and instead carry the diagnostic as
data, then render it. Once a diagnostic is data, i18n is choosing a message template by locale, the
Elm view is one renderer, and JSON is another.

## Decision

Model a diagnostic as a value (`souther.compiler.diag.Diagnostic`): a severity, an optional
code, a primary `Region`, optional secondary `Region`s each with a label, a message (a catalog key
plus arguments, or a compatibility literal), an optional found-vs-expected type pair, hints, and a
suggestion. A `DiagnosticRenderer` turns it into text — `HumanRenderer` (Elm-style, with color when
stderr is a TTY) or `JsonRenderer`. Prose comes from a `ResourceBundle` catalog: `messages_ja`
(the original default; revised above) over an English base (`messages.properties`); a key missing from Japanese falls back to
English, a key missing from both renders as itself, so the compiler never crashes on an unmigrated
site — the standing of that fallback is narrowed by the *Revision* above, which keeps it as a
fail-safe and forbids a shipped catalog from depending on it. Locale is resolved once: `--lang` > `SOUTHER_LANG` > the JVM default > Japanese — the last two steps
withdrawn by the *Revision* above. The code and
the type strings are locale-independent — the stable identity; titles, messages, hints, and labels
follow the locale.

`CompileException` now wraps a `Diagnostic`. Its `getMessage()` still returns the old one-line form,
so existing callers and tests are unchanged, while a renderer can take `diagnostic()` and produce the
snippet or JSON. An unmigrated throw site is wrapped as a `literal` diagnostic and renders through the
same pipeline immediately — a snippet and a localized frame, with the message body still the old
English string. The CLI (`compile` and `run`) gained `--format human|json`, `--lang`, and `--color`.

Two decisions bound the scope.

- Underlines are token-width, not full expression spans. `SourcePos` stays a point; a region is the
  point plus the offending token's length, computed at the throw site. The `Diagnostic` model is
  nevertheless region-capable (a `Region` is start-plus-end, and secondary regions are first-class),
  so an error that needs to point at more than one place — the two branches of a disagreeing `if`,
  the two sides of a failed composition — does so today, and precise multi-line spans can be added
  later without repainting the throw sites. Threading an end position through every AST node and
  every desugar pass was not worth its cost for a token-width default.
- The high-value errors are rewritten, the rest are migrated as-is. A handful of errors carry most
  of the felt quality — a type mismatch (found vs expected), an `if` whose branches disagree (each
  branch pointed at with its type), a non-exhaustive match (every missing case listed). These are
  written Elm-style with a `Type.show` that reads like source (`List<Int>`, `A | B`, `Int?`) rather
  than the record `toString`. The remaining ~148 messages move onto catalog keys mechanically, with
  the English literal as the fallback until each is translated.

## Consequences

- Every compile error renders Elm-style — titled, with a quoted line and caret — and in the selected
  locale, including sites not yet migrated onto a catalog key.
- `getMessage()` keeps its old text, so the ~30 tests that assert on message substrings stay green;
  the richer content lives on `diagnostic()`. The renderer's improved prose and the legacy one-liner
  can diverge until a site's tests are moved onto the structured diagnostic.
- A `code` and a `region` are available as JSON for an editor, CI, or agent; prose can be localized
  without breaking anything that keys on the code.
- Full Japanese coverage of all ~180 messages is a follow-through, not a single change: the mechanism
  and the high-value messages ship bilingual, and each remaining message becomes Japanese as it is
  migrated, falling back to English until then. That was how the coverage was reached; the *Revision*
  above makes the end state of it a requirement on every catalog that ships, so the next language
  arrives complete rather than filling in over releases.
- A multi-file build has no per-diagnostic file identity (SourcePos carries no file), so a snippet is
  quoted only for a single-file compile; a linked build renders the frame and message without the
  source line until a file handle is added to the position.

## Amendment: the file handle is on the position (issue #309)

The last consequence deferred a file handle on the position, and a compile worked out which file a
report belonged to from the question that found it instead. That holds while each question is about
one file and stops holding where it is not: a module's `example` rows, fake tables and values are
written in the module's own source and in any number of attached `examples for` files, and once they
are gathered under one name a question asked about the module can only answer with the module's own
file. What the author was then shown was the right line number quoted out of the wrong file — an
unrelated declaration with a caret in the middle of it.

So `SourcePos` now carries the source it was read from. It is given once, where a position is made
from a text (`LineIndex`), so no later pass has to reconstruct it, and it reaches every position a
parse makes without an AST walker. A position read from no source of this compile — a synthesized
node, the standard library, a module read back off the module path — names none, and a reader falls
back as it did before.

The source is part of what makes two positions the same position. Line 25 of two files is one
coordinate and is not one place, and a value whose identity denied one of its components would leave
"the same position" meaning something different in every container that held one — which is the
original mistake, re-expressible. Where coordinates alone are wanted, they are compared as
coordinates.
