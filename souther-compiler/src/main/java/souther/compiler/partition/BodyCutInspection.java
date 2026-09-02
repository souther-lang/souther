package souther.compiler.partition;


/**
 * What the rules written about a position, beyond the ends its own type states, came to.
 *
 * <p>The second phase of the cuts. A {@code guard} says where a behavior does something else, and
 * both sides of that line hold values a row can write — so a position its type left whole is
 * divided here, and a position nothing divides is one this phase also had nothing for.
 *
 * <p>Three answers and not two, for the reason the structural reading has three: a rule was
 * written about this position and could not be turned into a line, which is neither evidence nor
 * the absence of anything. Told apart, a report says what would have to change; run together, the
 * position comes back as one the model divides no way, which is the opposite of what the rule in
 * front of it says.
 *
 * <p><b>Whichever rule wrote it.</b> A {@code guard}'s comparison and a newtype's invariant are two
 * producers of one kind of evidence (spec §example-partition), so {@link NoLine} is what either of
 * them left the position with. The reader is told the same thing about both and does not have to
 * know which wrote it.
 */
public sealed interface BodyCutInspection {

    /** A rule drew a line through the position's values, and the axis carries it. */
    record Evidence() implements BodyCutInspection {}

    /**
     * The rules this phase read about the position were all understood, and none of them divided
     * it.
     *
     * <p>What was read, and not what could be written. A rule in a form no reader here takes apart
     * is {@link NoLine} and says so; a rule nothing looks for at all is neither, and no case of
     * this could say it. So this is a producer's answer about its own reading, which is what
     * anything reading it may say — never that no line exists at the position.
     */
    record Exhausted() implements BodyCutInspection {}

    /**
     * Rules are filed at the position and none of them came to a line, with what they established
     * between them.
     *
     * <p>Not a verdict on the position. Something else may still answer for it, and what this
     * settles is only that this phase did not.
     *
     * <p><b>Two answers and not one of two.</b> A position carries as many rules as its author
     * wrote, and a reading stopping on one of them says nothing about the one beside it — so both
     * are asked of the whole run and both are kept. Neither outranks the other here: what a verdict
     * needs is whether anything is unsettled, which is a projection, and a precedence would be this
     * phase deciding it. Written as "a rule is filed here", a comparison whose reading stopped and
     * one read from end to end came out alike, and the first went out as the model stating
     * something.
     *
     * <p><b>Both halves are read off what the readers left, and neither off a verdict.</b> A rule
     * read from end to end is a finding about the model; a rule whose reading did not finish is a
     * question about that rule, and this phase asks the questions standing at the place rather than
     * asking a word about the model which of the two happened.
     *
     * <p>Which rule it was is not here, and is not lost. A rule this phase could not use is a
     * {@link souther.compiler.inputs.RuleWithoutALine} made by the reader that read it, naming
     * which rule; carried through here as well, one limit at one position stood for however many
     * rules were stopped by it and the first of them was the one a report printed.
     *
     * @param aReadingStopped whether a rule filed here is one a reading did not get through, so
     *                        that what it would have divided the position by is not known
     * @param aRuleStatesSomething whether a rule filed here was read from end to end, which is the
     *                        model stating something at the position that came to no line
     */
    record NoLine(boolean aReadingStopped, boolean aRuleStatesSomething)
            implements BodyCutInspection {

        public NoLine {
            if (!aReadingStopped && !aRuleStatesSomething) {
                throw new IllegalArgumentException(
                        "no rule filed here is what Exhausted says");
            }
        }
    }

    /**
     * What this phase came to about one position, where it answered once per number the position is
     * measured at.
     *
     * <p>A location is measured at as many numbers as the rules name of it, and this phase answers
     * about each of those. What a report says about the location is one sentence, so the answers are
     * put together here rather than printed one apiece — a position is not divided no way twice
     * over.
     *
     * <p><b>What both of them found, and not whichever of them won.</b> A line anywhere means the
     * position is divided, whichever of its numbers the line is on; short of that, a rule filed at
     * one number of a location is filed at the location, and a reading that stopped on one is not
     * answered for by another that finished. So the answers are taken together and nothing is
     * chosen between them — which is what the name says, and what a precedence here would take
     * away. Written as one, a stop at one number and a rule read to the end at another came out as
     * whichever the walk met first.
     */
    static BodyCutInspection combined(BodyCutInspection first, BodyCutInspection second) {
        if (first == null) {
            return second;
        }
        if (second == null) {
            return first;
        }
        if (first instanceof Evidence || second instanceof Evidence) {
            return new Evidence();
        }
        if (first instanceof NoLine one && second instanceof NoLine other) {
            return new NoLine(one.aReadingStopped() || other.aReadingStopped(),
                    one.aRuleStatesSomething() || other.aRuleStatesSomething());
        }
        return first instanceof NoLine ? first : second;
    }
}
