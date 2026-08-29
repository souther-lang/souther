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
     * A rule was written about the position and this phase turned it into no line.
     *
     * <p>Not a verdict on the position. Something else may still answer for it, and what this
     * settles is only that this phase did not.
     *
     * <p><b>Which of the two ways that happened travels with it.</b> A reading that stopped and a
     * rule read from end to end that draws no line are opposite sentences about this compiler, and
     * this phase used to answer with neither — it said only that something was left, and the
     * verdict read that as a derivation this compiler could not make. So a {@code guard} relating
     * two positions, understood completely, came out as a position something is written at that
     * nothing read.
     *
     * <p>{@link LeftAtThePosition} and not a reason, because that is the same value the reading
     * before this one hands over: the two phases answer about one position, and a verdict has to
     * put their answers together without either being able to say more than it knows.
     *
     * <p>Which rule it was is not here, and is not lost. A rule this phase could not use is a
     * {@link souther.compiler.inputs.RuleWithoutALine} made by the reader that read it, naming
     * which rule; carried through here as well, one limit at one position stood for however many
     * rules were stopped by it and the first of them was the one a report printed.
     */
    record NoLine(LeftAtThePosition left) implements BodyCutInspection {

        public NoLine {
            if (left == null) {
                throw new IllegalArgumentException(
                        "a position left with nothing is what Exhausted says");
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
     * <p>A line anywhere outranks everything: the position is divided, whichever of its numbers the
     * line is on. Then a rule that came to nothing outranks the rules having been exhausted, for the
     * reason the arms are three and not two — a rule is written here, and saying the reading ran out
     * would be the opposite of what that rule says. Between two of those, whichever
     * {@link LeftAtThePosition#outranking} puts first.
     */
    static BodyCutInspection outranking(BodyCutInspection first, BodyCutInspection second) {
        if (first == null) {
            return second;
        }
        if (second == null) {
            return first;
        }
        if (first instanceof Evidence || second instanceof Evidence) {
            return new Evidence();
        }
        if (first instanceof NoLine(LeftAtThePosition one)
                && second instanceof NoLine(LeftAtThePosition other)) {
            return new NoLine(LeftAtThePosition.outranking(one, other));
        }
        return first instanceof NoLine ? first : second;
    }
}
