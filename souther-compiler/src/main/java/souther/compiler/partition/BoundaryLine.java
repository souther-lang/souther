package souther.compiler.partition;

import souther.compiler.check.RuleRef;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * One line a row can be written at, told from another.
 *
 * <p>The third of the three equivalences, and not a correction of either of the others. Which rule
 * it is is {@link RuleRef}'s and is the same value however many times the rule is read; which
 * reading of it drew a boundary is {@link OriginRef}'s; and this says which of those boundaries are
 * one line. They are three questions, and a reader that had one of them for another folded two
 * lines together or asked for a row twice.
 *
 * <p>Where the line is is part of it, and it has to be. One comparison written in a helper draws a
 * line wherever the helper is applied — {@code cap(a)} and {@code cap(b)} are one rule, drawn the
 * same way — and the lines are at different positions, so a row at one is not a row at the other.
 * Told apart by the rule and the drawing alone they fold into one, and a row is owed once for two.
 *
 * <p>Which reading drew it is not part of it, and that is the other half. A guard inside a
 * non-recursive helper is read once per call of that helper, so one line the author drew at one
 * position arrives as several origins — they carry different arms and a different comparison site,
 * each is a real occurrence measured on its own, and they are one line.
 *
 * <p>Here rather than on {@link OriginRef}, because a line is what a partition makes of an origin
 * and not something an origin knows about itself. Asked of it there, the folding read as the
 * origin's own identity, and the next thing to key on an origin keyed on the reading.
 *
 * @param target  where the line is
 * @param side    which of the values around the cut this one is
 * @param drawing whose rule drew it, and what the line it drew is
 */
public record BoundaryLine(BoundaryTarget target, BoundaryObligation.BoundarySide side,
                           Drawing drawing) {

    /**
     * Whose rule drew a line, and what the line it drew is.
     *
     * <p>Beside the rule rather than in it. Two boundaries of one rule at one value are two lines
     * where they answer these differently, since a row on the line is what shows them apart — and
     * none of them tells one rule from another, which is why the rule does not carry them.
     *
     * @param narrowedWithin the declarations a bound was taken in by, kept so that a narrowed line
     *                       stays apart from the bare one it narrows
     */
    public record Drawing(RuleRef rule, boolean valueBelongsBelow,
                          OriginRef.GuardOrigin.Witness witness, boolean holdsAtTheValue,
                          boolean singles, List<TypeSymbol> narrowedWithin) {

        public Drawing {
            narrowedWithin = List.copyOf(narrowedWithin);
        }
    }

    /** The line {@code obligation} asks for a row at. */
    public static BoundaryLine of(BoundaryObligation obligation) {
        return new BoundaryLine(obligation.target(), obligation.side(),
                drawnBy(obligation.origin()));
    }

    private static Drawing drawnBy(OriginRef origin) {
        return switch (origin) {
            case OriginRef.GuardOrigin g -> new Drawing(g.rule(), g.valueBelongsBelow(),
                    g.witness(), g.holdsAtTheValue(), g.singles(), List.of());
            case OriginRef.EnsuresOrigin e -> new Drawing(e.rule(), e.valueBelongsBelow(),
                    null, e.holdsAtTheValue(), e.singles(), List.of());
            case OriginRef.InvariantOrigin i ->
                    new Drawing(i.rule(), false, null, false, false, List.of());
            case OriginRef.NarrowedOrigin n -> {
                Drawing inner = drawnBy(n.bound());
                yield new Drawing(inner.rule(), inner.valueBelongsBelow(), inner.witness(),
                        inner.holdsAtTheValue(), inner.singles(), n.within());
            }
        };
    }
}
