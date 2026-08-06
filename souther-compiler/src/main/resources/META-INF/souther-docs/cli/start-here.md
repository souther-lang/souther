# Start here

If you have never written Souther, read these four in this order. Together they are about a
fifteen-minute read and cover everything needed to write a model that compiles.

1. `souther doc example` — a complete annotated model file. Read this first. It is the only place
   that shows a whole file at once, and it settles the shape of everything below.
2. `souther doc data` — how types are declared: newtypes with invariants, records, sums whose cases
   carry different fields, and field spread.
3. `souther doc behavior` — how a unit of business logic is declared and what its output sum means.
4. `souther doc control-flow` — `match`, `guard`, and how a pattern binds.

Then, when you need them:

- `souther api` with no argument prints the entire standard library in one screen. Read it once
  rather than searching it repeatedly.
- `souther api --source <Module>` prints a standard library module's own source, design comments
  included — the fastest answer to "why is this function shaped this way".
- `souther doc <error-code>` explains any diagnostic you hit, e.g. `souther doc e1918`.
- `souther doc --search <term>` ranks the specification by how much each section is about the term.

The specification is written to be read in full, and reads well that way. These four are the path
through it that gets you writing soonest, not a replacement for it.
