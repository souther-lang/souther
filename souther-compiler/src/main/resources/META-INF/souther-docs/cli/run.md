# Running a behavior: `souther run`

```
souther run <file.sou> [--behavior <name>] [--input <json>]
```

`souther run` compiles one self-contained `.sou` in memory and applies a single behavior to input
you give as JSON. It is itself the Java boundary: the input is decoded through the behavior's
derived decoders, the behavior runs, and the returned value is encoded back to JSON and printed.

It drives one file. Standard library imports resolve, but a file that imports another user module
cannot be run this way — compile both and call the generated classes instead.

## Which behavior runs

`run` runs a behavior that is both runnable and exposed.

It is runnable when it has a `let` and depends on nothing injected, or when it is a `>->` pipeline
whose stages are all runnable in that same sense.

It is exposed when the module's `exposing` list names it. `run` reaches a behavior the way any
reader outside the module does, so a runnable one the module keeps to itself is refused with that as
the reason. A file with no `exposing` list — a header-less `.sou` among them — keeps nothing to
itself, so everything runnable in it can be run.

With `--behavior` the named one runs. Without it, a module with exactly one behavior that is both
runs that one; if there are several, the run stops and lists them, and you pick one. A runnable
behavior the module does not expose is not among them, and naming it says so.

## How `--input` is encoded — the part that is easy to get wrong

The encoding depends on how many parameters the behavior takes.

| Parameters | What `--input` holds |
| --- | --- |
| none | nothing; omit `--input` |
| one | the argument itself, **not** wrapped in an array |
| two or more | a JSON array of exactly that many elements, positional |

So a one-parameter behavior over a `String` newtype takes `--input '"world"'`, not
`--input '["world"]'`. A two-parameter behavior takes `--input '[{"amount": 1200}, "2026-07-25"]'`.
Passing an array of the wrong length, or a non-array where several parameters are expected, stops
the run and says the arity it wanted.

A one-parameter behavior over a collection takes an array as its argument, so an array is not a
mistake by itself: `(xs: List<Int>)` takes `--input '[1,2,3]'`. Wrapping it — `--input '[[1,2,3]]'`
— is read as the argument array of the two-or-more form and stops the run, saying to remove the
outer array. What decides it is the decode: the text is read as the argument first, and only a text
that fails there while its sole element succeeds is the wrapped one.

Each element is decoded through the parameter type's own derived decoder, so it is written the way
that type's external form is written: a newtype is bare (`"world"`, `1200` — not `{"value": …}`), a
record is an object with its field names, a date is the string form `"2026-07-25"`.

A value in a sum-typed position carries a discriminator so the decoder knows which case to build;
{{doc:sum-discrimination}} says what that looks like.

## Examples

```sh
# one parameter
souther run hello.sou --behavior greet --input '"world"'

# two parameters
souther run billing.sou --behavior billFor \
  --input '[{"type": "Active", "id": "s-1"}, {"startsOn": "2026-07-01", "endsOn": "2026-07-31"}]'
```

## When you want the rules exercised instead

`souther run` answers "what does this do with this one input". To pin behaviour down as part of the
model, write `example` rows instead — they are checked at compile time and the compiler will tell
you what they leave uncovered. See {{doc:examples}} and `souther examples <file.sou>`.
