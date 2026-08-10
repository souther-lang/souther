# The `souther` command

```
souther <command> [args]
```

<!-- souther-section: compile -->
## compile

```
souther compile <file.sou>... -d <outdir> [-cp|--class-path <path>]
                              [--adequacy off|witness|all] [--warnings report|error]
```

Type-checks the given files together, resolving imports across them, and writes `.class` files
under `-d`. `-cp` (`--class-path`) points at modules another project compiled. `--adequacy`
additionally warns about what the `example` rows do not cover; it defaults to `off`, and `souther
examples` asks the same question as a report.

`--warnings error` refuses the build that warned: nothing is written and the exit code is non-zero.
It gates every warning and not only the adequacy ones, so a build that wants to fail on coverage
alone wants `souther examples --strict`, which refuses the same coverage findings and nothing else.
The default is `report`, which prints them and writes the classes.

<!-- souther-section: run -->
## run

```
souther run <file.sou> [-cp|--class-path <path>] [--behavior <name>] [--input <json>]
```

Applies one behavior of one file to JSON input and prints the JSON result. A file that imports
another user module runs against `-cp`, the same class path `compile` takes — compile that module
first and name where its classes went. The `--input` encoding depends on the behavior's arity and is
easy to get wrong — see {{doc:cli/run}}.

<!-- souther-section: fmt -->
## fmt

```
souther fmt <file.sou>... [-w|--write] [--check]
```

Prints the canonical form to stdout, rewrites in place with `-w`, or exits non-zero on a file that
is not formatted with `--check`.

`--check` prints each file it rejects as a unified diff against that file's canonical form. The
canonical form is what the verdict is taken against, so a failing build says what differs rather
than only which file did, and nothing has to be formatted a second time locally to read it. A file
already in canonical form is not mentioned.

<!-- souther-section: examples -->
## examples

```
souther examples <file.sou>... [-cp|--class-path <path>] [--module <name>]
                               [--behavior <name>] [--generate [--boundaries]] [--strict]
```

Reports how well the `example` rows cover the model — which partitions, boundaries and branch arms
no row reaches. `--generate` prints commented rows for what nothing covers, `--boundaries` adds
rows at the untried boundaries, and `--strict` exits non-zero on a gap the report names.

This is the command worth running on a model you believe is finished. It names gaps that reading
the rows does not reveal.

The report closes with two answers, and they are different questions. `measurement` says how much of
itself the measuring could make; `adequacy` says whether what it measured is covered. It is
`satisfied` where every measure that was asked for, and applies, came to an answer and none of them
found a gap; `not satisfied` (`not_satisfied` in the JSON) where one found a gap; and `undetermined`
where nothing that could find a gap was asked about, or one of those measures could not be made. A
measure that does not apply — the arms of a `>->` composition, which has none of its own — is neither
asked nor missing, and does not hold the answer open. `--strict`
refuses `not_satisfied` and nothing else, which is the same set of findings `compile --adequacy all
--warnings error` refuses. How many rows are waiting for a `let` is reported and never gated on:
waiting is the normal state of a model being written, and an injected behavior's recorded row is the
record of what that behavior owes.

<!-- souther-section: doc -->
## doc

```
souther doc [<anchor> | <error-code> | <set>/<topic>[/<section>] | --search <term> [--limit <n>]]
```

The language specification and the documentation bundled libraries ship. With no argument it lists
every section and topic as `name<TAB>title`. A shipped file that names parts of itself — by writing
`<!-- souther-section: name -->` above a heading — has each of them listed and read as
`<set>/<topic>/<name>`; one that names none is read whole. New to Souther? Read
{{doc:cli/start-here}}.

Every diagnostic code the compiler prints is the name of the section explaining it, in either case:
the `E2011` in a banner is {{doc:E2011}}. Nothing else has to be read off the banner for the
lookup to work.

A search asks three things in turn and stops at the first that answers. Whether the term is a name,
in which case that one document is the answer — the hyphens of a name are its spelling, so
`an-optional-does-not-stand-in-a-boundary` and `an optional does not stand in a boundary` are the
same question, and so is a diagnostic code. Whether the documents say the term as it stands, which
lists them. Whether they say its words, which lists them by how many of the words each one says.

<!-- souther-section: api -->
## api

```
souther api [<Module> | <Module>.<name> | --source <Module> | --search <term>]
```

The standard library's published surface with the signatures the type checker resolved. With no
argument it prints everything, which for a library this size is the fastest way to see it.
`--source` prints a module's own source with its design comments.

<!-- souther-section: japi -->
## japi

```
souther japi <class-or-package>[#<member>] [-cp|--class-path <path>]
```

A dependency's public API, read from its class files without loading them, with javadoc taken from
the `-sources.jar` beside the jar. This is the answer to "what does this library actually offer"
without disassembling anything.

A class name answers with every published member; `Class#member` answers with one of them, which is
what a class carrying sixteen overloads of the same name is worth asking. A compile-time constant is
printed with its value, since the value is what the declaration says.

```
souther japi net.unit8.raoh.Result#map2
```

<!-- souther-section: mcp -->
## mcp

```
souther mcp
```

Serves the `doc`, `api` and `japi` answers over the Model Context Protocol on stdio, for agent
harnesses that take tools rather than shell commands. The tools are `doc_search`, `doc_read`,
`stdlib_api`, `stdlib_api_search`, `stdlib_api_source` and `jar_api`.

Each tool publishes a capability rather than one spelling of an argument vector, because a client
here has no prompt to fall back to. `doc_read` with no `name` is the listing `souther doc` prints
for no argument, and `doc_search` takes the `limit` the flag takes. What `souther api` selects with
`--search` and `--source` is a tool each. `stdlib_api_search` answers every match, so it takes no
count.

The schema a client reads is the one the server enforces: every argument publishes its domain, and
one no tool declares is refused rather than dropped.

A document that sends its reader somewhere writes the operation rather than one caller's spelling
of it, so what a client is told to do next is a tool call and what a reader at a prompt is told to
do next is a command. A topic that documents an interface only one caller has is on that caller's
listing alone, and still read by name — `cli/run` is not on a client's map and answers when asked
for.

A long answer arrives in parts. Every tool hands back as much as one answer carries — at most
16,000 characters, the line saying how to carry on included — and ends with how much is left and
the `cursor` that reaches it; ask the same tool again with the same arguments and that `cursor`.
How much arrives at once is a question about this wire rather than about any one answer on it, so
the argument is on every tool and not only the ones expected to be long.

That line names the cursor and not the call, because the call is the caller's. Written back out, a
caller's own arguments would be inside an answer whose size this server is promising to bound, and
arguments can be longer than the bound.

A part stops where the document says to: a heading, failing that a blank line, failing that the end
of a line. A line or a code block longer than one answer carries has no such place in it, and is
cut where the count runs out — a bound a document could talk this server out of would not be one.

The cursor is this server's to read, so it goes out as it came in: where it points is checked
against the answer it is carried back to, and one measured against a different answer is refused
rather than resumed at.

<!-- souther-section: shared-options -->
## Options every command shares

| Option | Meaning |
| --- | --- |
| `--format human\|json` | how to render a compile error (default `human`) |
| `--lang <tag>` | message locale, e.g. `ja` or `en`. Overrides `SOUTHER_LANG`; with neither, `en`, which is what the shipped documents are written in |
| `--color auto\|always\|never` | color the human output (default `auto`) |

These apply to `compile`, `run` and `examples`. Passing them to another command is an error.

`--lang` chooses the language a compile error is written in, and nothing else. The documents `souther
doc` answers from are in English whichever language is chosen; a diagnostic's code is the same string
in every language, so it stays the name to look the answer up by.
