package souther.compiler.partition;

import souther.compiler.check.RuleRef;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * Which boundaries a partition folds into one line.
 *
 * <p>The third of the three equivalences, and not a correction of either of the others. Which rule
 * it is is {@link RuleRef}'s and is the same value however many times the rule is read; which
 * reading of it drew a boundary is {@link OriginRef}'s; and this says which of those boundaries are
 * one line to write a row at. They are three questions, and a reader that had one of them for
 * another folded two lines together or asked for a row twice.
 *
 * <p>A guard inside a non-recursive helper is read once per call of that helper, so one line the
 * author drew arrives as several origins. They carry different arms and a different comparison site
 * — each is a real occurrence and each is measured on its own — and they are one line. A rule that
 * is not a guard is its own line: nothing about an invariant or an {@code ensures} is read off a
 * body, so there is nothing there that expansion could have duplicated.
 *
 * <p>Here rather than on {@link OriginRef}, because a line is what a partition makes of an origin
 * and not something an origin knows about itself. Asked of it there, the folding read as the
 * origin's own identity, and the next thing to key on an origin keyed on the reading.
 *
 * @param rule            whose rule drew it
 * @param valueBelongsBelow which side of the line the cut value falls on, and the three beside it:
 *                        two boundaries of one rule at one value are two lines where they answer
 *                        these differently, since a row on the line is what shows them apart
 * @param narrowedWithin  the declarations a bound was taken in by, kept so that a narrowed line
 *                        stays apart from the bare one it narrows
 */
public record BoundaryLine(RuleRef rule, boolean valueBelongsBelow,
                           OriginRef.GuardOrigin.Witness witness, boolean holdsAtTheValue,
                           boolean singles, List<TypeSymbol> narrowedWithin) {

    public BoundaryLine {
        narrowedWithin = List.copyOf(narrowedWithin);
    }

    /** The line {@code origin} drew. */
    public static BoundaryLine of(OriginRef origin) {
        return switch (origin) {
            case OriginRef.GuardOrigin g -> new BoundaryLine(g.rule(), g.valueBelongsBelow(),
                    g.witness(), g.holdsAtTheValue(), g.singles(), List.of());
            case OriginRef.EnsuresOrigin e -> new BoundaryLine(e.rule(), e.valueBelongsBelow(),
                    null, e.holdsAtTheValue(), e.singles(), List.of());
            case OriginRef.InvariantOrigin i ->
                    new BoundaryLine(i.rule(), false, null, false, false, List.of());
            case OriginRef.NarrowedOrigin n -> {
                BoundaryLine inner = of(n.bound());
                yield new BoundaryLine(inner.rule(), inner.valueBelongsBelow(), inner.witness(),
                        inner.holdsAtTheValue(), inner.singles(), n.within());
            }
        };
    }
}
