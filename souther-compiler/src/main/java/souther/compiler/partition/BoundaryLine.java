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
 * <p>The line and not one of its points. Which of the four coverage items a row is at is
 * {@link PointRole}'s, and it used to be part of this — so the {@code ON} point and the
 * {@code OFF} point of one border were two lines, and nothing could ask what one border owed. Two
 * readings of one line owe the same four things, which is what makes this the key they are merged
 * under.
 *
 * @param target  where the line is
 * @param drawing whose rule drew it, and what the line it drew is
 */
public record BoundaryLine(BoundaryTarget target, Drawing drawing) {

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

    /** The line {@code border} is the coverage items of. */
    public static BoundaryLine of(Border border) {
        return new BoundaryLine(border.cut(), drawnBy(border.origin()));
    }

    private static Drawing drawnBy(OriginRef origin) {
        return switch (origin) {
            case OriginRef.GuardOrigin g -> new Drawing(g.rule(), g.valueBelongsBelow(),
                    g.witness(), g.holdsAtTheValue(), g.singles(), List.of());
            case OriginRef.EnsuresOrigin e -> new Drawing(e.rule(), e.valueBelongsBelow(),
                    null, e.holdsAtTheValue(), e.singles(), List.of());
            // A bound leaves nothing outside itself, so no value below or above it is a line of its
            // own and `valueBelongsBelow` has nothing to say. Whether the cut is one of the range's
            // own does have something to say, and telling two ends at one value apart by it is what
            // keeps a bound that admits the value from folding into one that stops short of it.
            case OriginRef.InvariantOrigin i ->
                    new Drawing(i.rule(), false, null, i.holdsAtTheValue(), false, List.of());
            case OriginRef.NarrowedOrigin n -> {
                Drawing inner = drawnBy(n.bound());
                yield new Drawing(inner.rule(), inner.valueBelongsBelow(), inner.witness(),
                        inner.holdsAtTheValue(), inner.singles(), n.within());
            }
        };
    }
}
