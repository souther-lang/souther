package souther.compiler.partition;

import souther.compiler.check.RuleRef;

/**
 * One line a row can be written at, told from another.
 *
 * <p>One of four equivalences and not a correction of any of them. Which rule it is is
 * {@link RuleRef}'s and is the same value however many times the rule is read; which line of the
 * model that rule drew is {@link AuthoredLine}'s; which reading of it drew a boundary is
 * {@link OriginRef}'s; and this says which of those boundaries a partition folds into one. A reader
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
 * which line of the model it is a reading of, and says so ({@link OriginRef#authoredLine}); what
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
 * @param target where the line is
 * @param line   which line of the model was drawn there
 */
public record BoundaryLine(BoundaryTarget target, AuthoredLine line) {

    /** The line {@code border} is the coverage items of. */
    public static BoundaryLine of(Border border) {
        return new BoundaryLine(border.cut(), border.origin().authoredLine());
    }
}
