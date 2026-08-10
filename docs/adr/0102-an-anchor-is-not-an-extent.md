# ADR-0102: An anchor is not an extent

Status: Accepted

## Context

A report that underlines an expression has to know how wide the expression is, and nothing in the
tree said. Every `Ast.Expr` carried one `SourcePos` and no second end, so the width was worked out
where the report was written — a table of node kinds, each measured from whatever that kind happened
to know:

```java
public static int width(Ast.Expr e) {
    return switch (e) {
        case Ast.Var v -> v.name().length();
        case Ast.StringLit s -> s.value().length() + 2;
        case Ast.Apply c -> c.written().length();
        default -> 1;
    };
}
```

There are 21 expression kinds. The table named seven and a companion `region` named three, so
fourteen were one column: a binary operation, a match, a construction, a comprehension, a list, a
tuple, every `let`, every attempt. Nineteen sites read one of the two, and the two disagreed about
the three kinds they both answered — `region(Var)` gave the occurrence the parser read, `width(Var)`
gave the length of the canonical name, which is short by however many combining marks the author
typed. The defect `AReportUnderlinesWhatTheAuthorTypedTest` was written to stop was fixed on one path
and live on the other.

Adding an end to each node would not have been enough, because for three kinds the position is not
where the expression begins. A binary operation is positioned at its operator, a field read at its
field, and an application built from a pipe at the callee on the right of it. Those are not
mistakes: a report about `+` belongs at `+`, and a report about a field that a value does not have
belongs at the field. A region built from such a position and any width at all starts in the middle
of what the author wrote.

The second half is the measuring. A width read off a decoded value is a claim about the value, and
the value parts company with the file wherever the source spells something the value does not keep.
`"2026-02-30\tx"` is fifteen characters and twelve, so the underline stopped one short of the closing
quote. A literal written with a decomposed kana is canonicalized to NFC as it is read, so it loses a
unit between the file and the value — the same failure with no escape in sight. `007` is three
characters and the number seven. `WrittenName.synthetic` did it too, taking the canonical name's
length at an anchor holding something else, which is a width for characters that are not there.

The CST has both ends of every node. `AstBuilder` read the first and dropped the second, and
downstream — with no way back to the tree the parser built — reconstructed what it could from what
each node still held.

## Decision

**Where a report is anchored and what it covers are two questions, and an expression answers both.
The extent is read off the CST and carried; it is never worked out from an anchor, from a semantic
value, or from the children a node was rebuilt from.**

`Ast.Expr` declares `Region region()` beside `SourcePos pos()`. The position is the anchor and stays
where it is, operator and field included. The region is the stretch of source the author wrote the
expression over, read once in `AstBuilder` from the first and last meaningful token under the node.

Parentheses are part of the extent. `PAREN_EXPR` is reduced away — the tree keeps the expression
inside it — and the characters are still in the file, so the reduced node is stamped with the
bracketed node's own region. What is preserved is the widest stretch the author wrote there: a
report that wants the operator or an operand selects it, and no report can widen an extent that was
never kept.

A node no one wrote has no extent. `region()` is null rather than a zero-width region at the anchor,
because "there is nothing to underline" and "underline no characters at this place" are different
answers, and only the first is true of a binding a lowering introduced. `WrittenName` says the same
thing the same way: a synthetic name keeps an anchor and holds no segments, so it has somewhere a
complaint belongs and nothing that spells it.

Reports read `reportedAt()`, which is the extent where there is one and a point at the anchor where
there is not. It chooses between two answers already held and computes no third.

A pass carries the extent or replaces it, and does neither by accident. Every rewrite passes the
node's own region through, and `FieldInit` and `FieldAccess` gained `withValue` and `withTarget` so
that a rewrite of what a form holds cannot re-spell the name it was written with — three passes did,
which turned an occurrence the author made into a synthetic name and a fabricated width. Where a body
is copied out of another module, the existing rule decides: `HelperInliner.keepsItsPositions` already
stamped a prelude body with the call site so an error inside it points at the user's call, and that
rule now stamps the extent as well as the point. It is the same policy carried to the new value, not
a second one.

`Elaborator.region` and `Elaborator.width` are deleted.

### What was weighed

*Move `pos` to the start of the expression.* It makes the region trivial to build and costs the
anchor: `+`, the field, and the callee of a pipe are each the place a report about that node belongs,
and there would be nowhere left to say so. It also changes what every existing report points at, for
a reason that has nothing to do with any of them.

*Add an end beside the position.* `new Region(e.pos(), e.end())` is wrong for exactly the kinds whose
position is not their start, which is where the defect was worst.

*Keep the table and fix the cases.* The kinds that were one column would each need a rule, and every
rule would be a measurement — the thing that is wrong. It also leaves the next kind added silently at
one column.

*Fix the literals and leave `WrittenName.synthetic`.* The fabricated width there is the same rule
broken in the same way one abstraction over. Left standing, what this changed is one call path rather
than the rule.

## Consequences

Every `Ast.Expr` record gained a component and roughly 190 construction sites say what they mean by
it. There is no default: a pass that mints a node writes `null` and says so, the way
`ConstructionOrigin` already has no default for the same reason.

`Var` is the one kind whose extent is not its own component in the ordinary case — its constructor
takes it from the `WrittenName` it holds, because a name is the whole of that expression. It is a
component all the same, since a parenthesized name is one expression written over more characters
than the name is, and the constructor refuses a region that does not contain the name's own.

`HumanRenderer` draws one caret under a region that ends on a later line, as it did before. The
extent an expression now carries is right for a multi-line expression and what a terminal draws under
it is not yet; a published region and an editor reading one get the whole of it today.

Two rows of `ADiagnosticPointsAtTheOperandThatSuppliedTheValueTest` expected an argument to be
underlined as far as its callee's name. They now expect the argument.

## References

- `[#compile-errors]` — what a report points at
- Issue #612 — an expression starts somewhere and ends nowhere
- ADR-0095, ADR-0096 — a name is one text however it is spelled, and a column is a code unit
- ADR-0101 — a diagnostic says the values it carries; a position is a `Region` and not one of them
