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
 * producers of one kind of evidence (spec §example-partition), so {@link Blocked} is what either
 * of them was left unread as. The reader is told the same thing about both and does not have to
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
     * is {@link Blocked} and says so; a rule nothing looks for at all is neither, and no case of
     * this could say it. So this is a producer's answer about its own reading, which is what
     * anything reading it may say — never that no line exists at the position.
     */
    record Exhausted() implements BodyCutInspection {}

    /**
     * A rule was written about the position and nothing here turned it into a line.
     *
     * <p>Not a verdict on the position. Something else may still answer for it, and what this
     * settles is only that this phase did not.
     *
     * <p>It carries no reason, and the reason is not lost. A rule this phase read and could not use
     * is an {@link souther.compiler.inputs.RuleWithoutALine} made by the reader that read it, naming
     * which rule; carried through here as well, one limit at one position stood for however many
     * rules were stopped by it, and the first of them was the one a report printed.
     * What this phase owes the verdict is whether it drew anything, which is the whole of what
     * three cases say.
     */
    record Blocked() implements BodyCutInspection {}
}
