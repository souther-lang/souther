# The `souther` command

```
souther <command> [options] [args]
```

`souther help` lists the commands, and `souther help <command>` writes one command's arguments and
every option it takes. That listing is generated from the same table the compiler resolves an option
against, so it says what this build does rather than what a text was last edited to say.

<!-- souther-section: init -->
## init

```
souther init [<groupId>:<artifactId>] [-d|--dir <path>] [--build maven|gradle]
                                      [--model none|minimal|full] [--module <name>]
```

Writes a project, or adds Souther to one that is already there. Never interactive, and nothing
already written is overwritten — a second run finishes what a first one left, and says which files it
left alone.

Where there is no build file, a project is created and the coordinate is required: a group and an
artifact are a person's decision, and neither a directory name nor a git remote makes it. `--dir`
says where it goes, and defaults to the artifact.

```
$ souther init com.example:hello
    created  hello/pom.xml
    created  hello/.gitignore
    created  hello/src/main/souther/hello.sou
             module com.example.hello
    created  hello/src/main/souther/hello.examples.sou
    created  hello/src/test/java/com/example/hello/ReturnBookTest.java

    cd hello && mvn test
```

`--build gradle` writes `settings.gradle.kts` and `build.gradle.kts` instead, and no wrapper: a
wrapper pins a Gradle version, and a version pinned when this compiler was released is one it can
never revisit. It says to run `gradle wrapper` first.

The generated Gradle build names no Souther version, where the Maven one names the version of the
compiler that wrote it. On Gradle the plugin adds the runtime at the version it compiles with, so
there is no second number in the build script to keep in step — and the version it compiles with is
the one that plugin release was verified against, which need not be the one that ran `souther init`.
Write it to say which:

```kotlin
souther {
    southerVersion = "0.1.0-rc5"
}
```

Where a `pom.xml` or a `build.gradle.kts` is already there, the coordinate is read out of it rather
than written on the line, `--build` is not read — the build that is there is the build — and what is
added is a source directory and the plugin declaration. The previous contents of the build file are
left in a `.orig` beside it, unless git is already holding them.

The module header follows from the coordinate: the group and the artifact, with a hyphen written as
an underscore, so `com.acme:billing-service` writes `module com.acme.billing_service`. That name is
also the Java package the model generates into, and the source is named after its last segment —
`src/main/souther/billing_service.sou`. `--module` writes another.

`--model` says how much of a model to start with, and defaults to `full` where a project is created
and `none` where one is added to. `none` is the module header; `minimal` adds one `data` with an
`invariant`; `full` is a model that uses `data`, `invariant`, `behavior`, `constructs` and `guard`,
with an `.examples.sou` covering it and a Java test that reaches the generated types — so that both
`mvn test` and `souther examples` answer on the first run.

<!-- souther-section: compile -->
## compile

```
souther compile <file.sou>... -d|--dir <outdir> [-cp|--class-path <path>]
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

`--check` prints each file it rejects as the rules it differs by: a line naming the rule, the place
in your own source, and the two answers — what the canonical form does there and what your file
does.

```
m.sou:5:11: a construct written down the page breaks at every place it settles
    the canonical form: one line ends here; this source: no line ends here
```

A rule and not a diff. A diff says which characters moved and cannot say why any of them did, so a
reader who wants to write the canonical form rather than have it written for them had to work the
rule out from the characters. The canonical form is still what the verdict is taken against, so
nothing has to be formatted a second time locally to read the report. A file already in canonical
form is not mentioned.

Where a difference is one no rule accounts for yet, the report says so and shows the rest as a
unified diff. A list that named what it can and stopped would read as a file with these differences
and no others.

Every rule a line can name is written down under "The words the report uses" below, and read on its
own with `souther doc cli/commands/fmt-report-vocabulary`.

### What the canonical form is

The formatter derives the layout rather than keeping yours. Two of the things you wrote are
structure and not layout, and it keeps those: where a paragraph break is, and what a comment was
written about. Everything else is derived. So there is one form per program taken with those two —
write the same program with the same paragraphs and the same comments and the same text comes back,
however differently the rest of it was laid out.

These are the rules it derives it by, so that what the tool will write can be read here rather than
reconstructed from having run it.

Lines are at most 100 columns and a nesting level is 4 spaces. A line longer than 100 columns is one
whose content holds nowhere to break — a long string, a comment, a single long name, a nesting deep
enough that the indent takes the width. That is not an exemption for some constructs: everything
that has a boundary to break at breaks at it, and a 130-column `unreachable` message survives only
because a string literal has none.

A column is a column on the screen and not a character. A character East Asian Width calls wide or
fullwidth — every CJK ideograph, kana and hangul syllable, and the fullwidth forms — is two columns,
every other character is one, and a tab advances to the next column that is a multiple of 8. So a
name written in Japanese takes twice the width its characters suggest, and a line of them fits half
as many. This is a convention the formatter states rather than a reading of your terminal: the
canonical form of a file has to be the same file whatever it is being looked at in.

Where a blank line goes is yours; how big it is is not. Between two top-level items, and between two
steps of a block, one blank line comes back as one and three come back as one, and none stays none —
so a run of related one-line declarations stays a run and a body written as paragraphs keeps them.
Two places are the file's rather than yours and get a blank line whatever you wrote: under the header
a file opens with — a `module` or an `examples for` — and under the last import. Nothing else is
kept: a blank line inside a construct, between the fields of a `data` or the arms of a `match`, is
not a paragraph break and does not survive.

A `data` product body writes each field on a line of its own, opening the line with the `{` for the
first and with a `,` for the rest, and closing with a `}` at the body's own indent. It is written
that way whenever it has a field, whether or not it would fit on one line; a body with no fields is
`{}`.

```
data Employee =
    { id: EmployeeId
    , rank: Rank
    }
```

Everything else written between brackets — a record literal, an argument list, a type argument list,
a tuple, a list literal, the names in `exposing` and `import` — fits or breaks as one thing: written
on one line where it fits and one member to a line where it does not, each line but the last ending
with its `,`. No trailing `,` is written before the closing bracket in either case. A behavior's
parameter list is the exception and is laid out with the signature holding it, below.

```
let e = Employee { id = EmployeeId("e-1"), rank = Staff }

let wide =
    Employee {
        id = EmployeeId("an-identifier-long-enough-that-the-literal-does-not-fit-on-one-line"),
        rank = Staff
    }
```

So the two conventions are the constructs' and not the file's: a `data` body opens its lines with
the comma and everything else closes them with it.

A behavior signature lays its inputs and its output out together, so neither is decided on its own.
Where the whole signature fits, it is one line. Where it does not, the parameter list breaks first —
one parameter to a line, with the `)` opening the line the output is written on — and the output
union breaks only where it still does not fit that line. A parameter list short enough for a line of
its own is therefore written down the page anyway when what follows the arrow leaves it no room:
inputs give way before the output, so that a signature keeps its three parts whole for as long as it
can rather than leaving the first member of a union on the signature line beside the arrow.

```
behavior fits : (a: A, b: B) -> X | Y

behavior preApprove : (
    request: AwaitingPreApproval,
    approverId: EmployeeId
) -> PreApproved | NotAuthorized

behavior judge : (
    code: Code
) -> AcceptedByTheUnderwriter
    | RefusedByTheUnderwriter
    | DeferredForManualReview
    | EscalatedToTheManager
```

A `guard` reads the same way and gives way in the same order. Where it fits, it is one line. Where
it does not, the `else` opens a line under it — the departure is what the guard is for, and left to
the condition's own breaking it ends up at the end of whichever continuation line the last conjunct
took. The condition breaks after that, and only where it does not fit the line the `guard` left it.

```
    guard List.length(rows) >= 1 else NoRows

    guard List.allDistinctBy(x -> x, rows) && List.length(rows) >= 1 && Foo.baaaaaaaar(rows)
        else NoRows

    guard List.allDistinctBy(x -> x, rows)
        && List.length(rows) >= 1
        && List.length(rows) < 100
        && Foo.bar(rows)
        else NoRows
```

A `guard` whose departures are named clauses is written the other way round, because there is no one
departure to break off: the `else` ends the guard's own line and the clauses go under it.

```
    guard Lines(rows) as items else
        | nonEmpty -> NoRows
        | unique -> DuplicateProduct
```

An `example` and a `fake` are decision tables, and their rows are read against each other: which
input differs between two rows is what writing them one under the other is for. So the connectors of
a table's rows are written at one column — the `:` and the `->` of an `example`, the `->` of a
`fake` — with the shorter rows padded out to the widest. Adding a row rewrites the table where the
new one is the widest, which is the diff a table asks for. Whatever the author lined up by hand is
derived again like everything else, and a row too long for one line is written down the page and
takes no part in the columns. The padding is measured in columns on the screen, so a table whose
descriptions are Japanese lines up on a screen rather than on a character count, and it is written
as spaces — a tab reaches a column too, and what a source wrote there is the rule about what goes
between two tokens' to say rather than the column's.

```
example priceOfTheFirstGlass
    | "off peak, no coupon" : (OffPeak, NoCoupon)     -> Price(490)
    | "happy hour"          : (HappyHour, NoCoupon)   -> Price(290)
    | "with a coupon"       : (OffPeak, WithCoupon)   -> Price(100)
```

A comment keeps what it was written about. On the line of the code it follows it stays there; on a
line of its own it goes above what follows it, unless a blank line separates it from that and none
separates it from the code above, in which case it stays under that code. A comment with nothing
after it closes whatever holds it.

<!-- souther-section: fmt-report-vocabulary -->
### The words the report uses

`--check` writes its own words, and a reader who wants to know what one of them means has nowhere to
look it up unless it is written down. A diagnostic carries a code and a code names a section; a line
of this report carries neither, so its vocabulary is fixed here. These are all of the rules a line
can name, and nothing else is one.

Which tokens are written. Asked first, because which tokens there are settles what boundaries the
rest of the rules are about:

- a comma-separated run is written without a comma after its last member — the two answers quote the
  comma and the nothing that stands where it would.
- a match writes every arm with its bar — including the first, which a source may leave off.
- a definition writes its parameters to the left of the `=` — rather than as a lambda to the right
  of it.

What stands between two tokens the same line holds:

- what goes between two tokens on a line — one space, or none. The two answers quote the characters,
  so a source that wrote a line break where neither text ends a line reads it back as `\n`. At a
  table's column this answers about the separator and the column rule about the padding after it,
  so what is written there is this rule's until the separator is what the canonical form has —
  a tab, or no space at all, is quoted here rather than reported as a column the row missed.

Whether a construct is written down the page at all. The two answers are `on one line` and `down the
page`, and which rule is named is which one decided the form:

- a construct whose line would exceed the width breaks — named only where the width decided it.
- a construct written down the page writes its members one to a line — the construct holds something
  that cannot share a line with what follows it, so no width would have kept it whole.
- a bracket of a construct written down the page takes a line of its own — the same, for the bracket
  rather than the members.
- nothing shares a comment's line — a comment ends the line it is on, which is why a construct
  holding one is never written flat.

The last three of those answer about one boundary as well as about the whole construct, and the two
answers say which they are about. `on one line` against `down the page` is the construct: the two
texts write it in different forms. `one line ends here` against `no line ends here` is one of the
boundaries under it, asked where the forms agree and a single place does not.

Where a construct written down the page breaks. Both texts write it down the page and the source ran
one of its places together; the line stands at that place, and the two answers say whether a line
ends there:

- a construct written down the page breaks at every place it settles — some of its places were run
  together, whatever put the construct down the page.
- a group written down the page ends one line where it breaks — the same place, asked about how many
  lines end at it rather than whether one does.

How far in a line begins. The two answers are columns:

- one level deeper is one indent further in — a step, and not a column the rule never states.
- a line the file holds begins at column zero — the outermost level, which has no level outside it
  to be measured from.

Where a table's rows line up. An `example` and a `fake` write the connectors of every row at one
column, and the two answers are columns:

- the rows of a table of examples write their : at one column — the description was padded out to
  the widest one in the table, or was not.
- the rows of a table of examples write their -> at one column — the same, for the input.
- the rows of a table of fakes write their -> at one column — a `fake` has the one column, since its
  rows have no description.

The column a row is said to be at is where the padding it wrote carries it, with the rest of the
line as the canonical form has it. So a table lined up correctly and indented one column too deep is
told about its indentation and nothing else, rather than about every row.

What separates one thing from another, and what ends:

- a blank line stands where the author wrote one, and under a header — how many, as lines.
- a line ends where what is written on it does — nothing stands after it.
- a file ends with one newline.

Comments:

- a comment at the end of a line is written one space after the code.
- a comment on a line of its own is written above the line it owns.
- a comment is carried by the construct it was written against — this one answers with where the
  comment goes rather than with what stands there.

A rule is named where a source departs from it, so a rule missing from a report is one the file
already writes. What no rule here accounts for is not left out: the report says so and shows it as a
diff.

<!-- souther-section: examples -->
## examples

```
souther examples <file.sou>... [-cp|--class-path <path>] [--module <name>]
                               [--behavior <name>] [--generate [--boundaries]] [--strict]
```

Reports how well the `example` rows cover the model — which partitions, boundaries and branch arms
no row reaches. `--generate` prints commented rows for what nothing covers, `--boundaries` adds
rows at the untried boundaries, and `--strict` exits non-zero on a gap the report names.

A generated row leaves the answer as `<?>`, and where the behavior carries an `ensures`, part of that
answer is already written down. So the clauses are quoted over the rows of the behavior they are
written on, in the author's own words, cut out of the source. They are quoted whether or not this
compiler could make a rule of them, which is all the heading claims: these are the words in the
declaration.

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
--warnings error` refuses.

The report prints more findings than a build refuses over, and says which is which. A line under `!`
is one of them; a line under `·` is something measured and named and not gated on — a class no row is
in, a position the model divides no way. The two read alike and are a sentence apart: `no row uses
`C`` is refused over and `no row is in `C`` is not, and writing a row for `C` closes both. The count
under `adequacy` is how many are marked. In the JSON each behavior carries `findings`, where every
one of them says its `kind` and what a build does about it under `disposition` — `refused`,
`reported`, or `undecided` where the measure behind it came to no answer.

How many rows are waiting for a `let` is reported and never gated on:
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

<!-- souther-section: help -->
## help

```
souther help [<command>]
```

What this command line takes. With no argument it lists every command with a line saying what it is
for; with a command it writes that command's arguments and every option the command takes, each with
what the option means there. `souther <command> --help` asks the same thing and is answered the same
way, and so is `-h`.

The answer goes to stdout under a zero exit code. Everything this writes used to be reachable only
from a failure — no command, an unknown one, a missing argument — so it went to stderr and the exit
code said the line was wrong. Reading it meant writing a line you knew would be refused, and piping
it anywhere gave you an empty pipe.

A section lists the options the compiler will resolve against that command, so an option two
commands take is written under both. `--behavior` is `run`'s and `examples`', and what it selects is
not the same question in the two of them: it chooses which behavior `run` drives, and narrows what
`examples` reports on. Each section says the one that holds there.

`--help` outranks what is wrong with the line. `souther compile --nonsense --help` writes compile's
section and exits zero rather than refusing the option, because a line asking what a command takes is
asking for the reason it is wrong. What does not ask is a line where the token stands in an option's
value: `souther run m.sou --input --help` hands `run` the input `--help`, and that is read as the
value it is, not as a request.

<!-- souther-section: shared-options -->
## Options every command shares

| Option | Meaning |
| --- | --- |
| `--format human\|json` | how to render a compile error (default `human`) |
| `--lang <tag>` | message locale, e.g. `ja` or `en`. Overrides `SOUTHER_LANG`; with neither, `en`, which is what the shipped documents are written in |
| `--color auto\|always\|never` | color the human output (default `auto`) |
| `--help`, `-h` | what this command takes, and what its options mean |

`--help` and `-h` are taken by every command, including `help` itself. `--format` and `--color`
apply to `compile`, `run` and `examples`; `--lang` to those and to `init`, which writes what it did
in the language the line asks for. Passing one of them to a command that does not take it is an
error.

Because every command takes `-h`, no command reads that token as a file name. A single dash is
otherwise read as a path by any command that has no such option — a file may be named `-d` — and
this is the one short option that rule no longer reaches.

`--format` and `--color` take the values written above and no others. A value outside the set is
refused rather than read as the default: a caller that asked for `--format jsn` was answered with a
human snippet and the exit code the JSON run gives, which is the answer to a question they did not
ask.

`--lang` is not a closed set in the same way. What it takes is a language tag, and a language this
compiler ships no catalog for is answered from the English base — `fr` is a language somebody may
read, and that nobody has translated the messages into yet is not a mistake in what they wrote. What
is refused is a tag that is not one: `--lang en-!!` named nothing after `en`, and was read as `en`
with the rest dropped. `_` is accepted where `-` belongs, so a POSIX-style `ja_JP` names Japanese in
Japan; what that produces is held to being a language tag like any other, so `ja_JP.UTF-8` is
refused rather than read up to the codeset.

`SOUTHER_LANG` names a language the same way and is held to the same tags, and a refusal says which
of the two was written. Only the value the precedence chose is read: with `SOUTHER_LANG` set to
something that is not a tag, a line writing `--lang en` compiles, because the variable is not what
named the language.

What counts as naming one differs between the two. A shell unsets a variable by exporting it empty,
so a blank `SOUTHER_LANG` is a variable nobody set. A blank `--lang` is not a line that left the
option out — somebody wrote a value where a language goes — so it is refused, rather than answered
under whatever the environment says.

`--color` is read where the human renderer is built, and `--format json` builds the other one, so a
line that writes both is refused. It is refused whichever value `--color` was given, `auto` included:
the default in force where nobody wrote the option and the same value written out are not the same
statement, and a line that asked for a colour policy is told that nothing here reads one rather than
being answered as though it had asked for nothing. The refusal is what says it because the JSON
stream cannot: it is one diagnostic per line and a sentence among them is a line its reader parses as
nothing.

`--lang` chooses the language a compile error is written in, and nothing else. The documents `souther
doc` answers from are in English whichever language is chosen; a diagnostic's code is the same string
in every language, so it stays the name to look the answer up by.
