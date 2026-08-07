# The `souther` command

```
souther <command> [args]
```

<!-- souther-section: compile -->
## compile

```
souther compile <file.sou>... -d <outdir> [-cp <path>] [--adequacy off|witness|all]
```

Type-checks the given files together, resolving imports across them, and writes `.class` files
under `-d`. `-cp` points at modules another project compiled. `--adequacy` additionally warns about
what the `example` rows do not cover; it defaults to `off`, and `souther examples` asks the same
question as a report.

<!-- souther-section: run -->
## run

```
souther run <file.sou> [--behavior <name>] [--input <json>]
```

Applies one behavior of one self-contained file to JSON input and prints the JSON result. The
`--input` encoding depends on the behavior's arity and is easy to get wrong — see
{{doc:cli/run}}.

<!-- souther-section: fmt -->
## fmt

```
souther fmt <file.sou>... [-w] [--check]
```

Prints the canonical form to stdout, rewrites in place with `-w`, or exits non-zero on a file that
is not formatted with `--check`.

<!-- souther-section: examples -->
## examples

```
souther examples <file.sou>... [-cp <path>] [--module <name>] [--behavior <name>]
                               [--generate [--boundaries]] [--strict]
```

Reports how well the `example` rows cover the model — which partitions, boundaries and branch arms
no row reaches. `--generate` prints commented rows for what nothing covers, `--boundaries` adds
rows at the untried boundaries, and `--strict` exits non-zero while rows are still waiting.

This is the command worth running on a model you believe is finished. It names gaps that reading
the rows does not reveal.

<!-- souther-section: doc -->
## doc

```
souther doc [<anchor> | <set>/<topic>[/<section>] | --search <term> [--limit <n>]]
```

The language specification and the documentation bundled libraries ship. With no argument it lists
every section and topic as `name<TAB>title`. A shipped file that names parts of itself — by writing
`<!-- souther-section: name -->` above a heading — has each of them listed and read as
`<set>/<topic>/<name>`; one that names none is read whole. New to Souther? Read
{{doc:cli/start-here}}.

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
souther japi <class-or-package>[#<member>] [-cp <path>]
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

A long answer arrives in parts. `doc_read` hands back as much as one answer carries, ending with
how much is left and the call that reaches it; carry that `cursor` back with the same `name`. The
cursor is this server's to read, so it goes out as it came in: where it points is checked against
the answer it is carried back to, and one measured against a different answer is refused rather
than resumed at.

<!-- souther-section: shared-options -->
## Options every command shares

| Option | Meaning |
| --- | --- |
| `--format human\|json` | how to render a compile error (default `human`) |
| `--lang <tag>` | message locale, e.g. `ja` or `en` (default: the system's, then `ja`) |
| `--color auto\|always\|never` | color the human output (default `auto`) |

These apply to `compile`, `run` and `examples`. Passing them to another command is an error.
