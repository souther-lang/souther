package souther.compiler.partition;

import souther.compiler.check.RuleRef;

import java.util.Objects;
import java.util.Optional;

/**
 * One line a row can be written at, told from another.
 *
 * <p>One of four equivalences and not a correction of any of them. Which rule it is is
 * {@link RuleRef}'s and is the same value however many times the rule is read; which line of the
 * model that rule drew is {@link AuthoredLine}'s; which reading of it drew a boundary is
 * {@link LineOrigin}'s; and this says which of those boundaries a partition folds into one. A reader
 * that had one of them for another folded two lines together or asked for a row twice.
 *
 * <p>Where the line is is part of it, and it has to be. One comparison written in a helper draws a
 * line wherever the helper is applied — {@code cap(a)} and {@code cap(b)} are one rule, drawn the
 * same way — and the lines are at different positions, so a row at one is not a row at the other.
 * Told apart by the rule and what it drew alone they fold into one, and a row is owed once for two.
 *
 * <p>Which reading drew it is not part of it, and that is the other half. A guard inside a
 * non-recursive helper is read once per call of that helper, so one line the author drew at one
 * position arrives as several origins — they carry different arms and a different comparison site,
 * each is a real occurrence measured on its own, and they are one line.
 *
 * <p><b>Which authored line it is, and not the folding, is asked of the origin.</b> A reading knows
 * which line of the model it is a reading of, and says so ({@link LineOrigin#authoredLine}); what
 * this adds is where that line was read, which is the position and behavior a row would be written
 * for. The folding stays a partition's answer rather than an origin's, so that what an origin
 * answers about itself is never the key something else groups it by.
 *
 * <p><b>So a debt is what is left when the position goes.</b> Two borders under one of these are
 * one {@link BorderObligationId} by construction: this holds the authored line and where it was
 * read, and a debt holds the authored line and the value it is at. Folding readings into a line
 * therefore never folds two debts together, which is what {@code Coverages} holds itself to when it
 * merges what each reading saw. The converse does not hold and must not: one authored line is read
 * at as many positions and behaviors as carry the rule, and every one of them is the same row to
 * write.
 *
 * <p>The line and not one of its points. Which of the four coverage items a row is at is
 * {@link PointRole}'s, and holding it here makes the {@code ON} point and the {@code OFF} point of
 * one border two lines, leaving nothing to ask what one border owes. Two readings of one line owe
 * the same four things, which is what makes this the key they are merged under.
 *
 * <p><b>And how the reading's points stand to the author's.</b> A comparison a body wrote can be put
 * at one place on one quantity facing its author's sides two ways ({@link AuthoredPlacement}), and
 * there the run on one side of the place is one of the author's points in one reading and another
 * in the other. Merged point by point, what a row showed about the one would be counted for the
 * other. Readings that face the author's line alike are merged, however many calls made them.
 *
 * <p><b>And which threshold of which computation.</b> Two calls of a helper cut at different places
 * are two computations, and the bound each is held against is that computation's own: readings
 * of them put at the same place are not one line, whatever number their bounds come to, since the
 * rows that stand beside one are not the rows beside the other. This is the same threshold a
 * point of the line is owed at ({@link BorderObligationPoint.AtLine}).
 *
 * @param target    where the line is
 * @param line      which line of the model was drawn there
 * @param placement how the points of the line drawn there are the points of the author's
 * @param threshold which threshold of a derived value the line is, where it is one
 */
public record BoundaryLine(BoundaryTarget target, AuthoredLine line, AuthoredPlacement placement,
                           Optional<ThresholdOfADerivedValue> threshold) {

    public BoundaryLine {
        Objects.requireNonNull(threshold, "no threshold is Optional.empty()");
    }

    /** A line that is no threshold of a derived value. */
    public BoundaryLine(BoundaryTarget target, AuthoredLine line, AuthoredPlacement placement) {
        this(target, line, placement, Optional.empty());
    }

    /** The line {@code border} is the coverage items of. */
    public static BoundaryLine of(Border border) {
        return new BoundaryLine(border.cut(), border.origin().authoredLine(), border.placement(),
                border.threshold());
    }
}
