package souther.compiler.check;

/**
 * A question about the model that one of its rules raises, and that something has to answer before a
 * measure may say the rule was read.
 *
 * <p>Not a reader, and this is the whole point of the type. A reading is one way of answering one of
 * these; which readings there happen to be is a fact about this compiler, and a completeness written
 * as "every reader ran to the end" says the model was read in full only for as long as nobody adds a
 * reader. Written as questions, a reader gained answers an existing one and a reader lost leaves the
 * question standing with nothing against it — which is what a report is for.
 *
 * <p>Each carries the subject it is about, because they are not the same subject and a report that
 * used one for the other named the wrong thing. What values may stand somewhere is about a position;
 * where a line falls is about a number taken of one, and a {@code String} bounded on its length is
 * measured at the length while its values are the string's.
 *
 * <p><b>Only the questions {@link souther.compiler.inputs.InputDomain} can issue today.</b> Not a
 * list of the questions a measure of coverage could conceivably ask: an arm nothing raises is a
 * question every model answers by nobody having asked it, and a completeness counted over such a set
 * says more than it knows. A rule shape gaining a question here is the same change that starts
 * raising it — the two arrive together or the second is a design note wearing a type's clothes.
 */
public enum CoverageObligation {

    /**
     * Which values may stand at a position.
     *
     * <p>Subject: the position. Answered by a reading that turns a rule into a set of values, and
     * answered as readily by one that turns the same rule into where the values stop — an end is a
     * statement about which values may stand there, and a rule read into an end is not a rule
     * nothing took in. Which of the two answered is this compiler's business; that one of them did
     * is the model's.
     */
    ADMITTED_VALUES,

    /**
     * A line rows are owed at.
     *
     * <p>Subject: the number the position is measured at. Raised by every rule that places an end,
     * whether it divides the position or only stops it.
     */
    BOUNDARY,

    /**
     * Classes a row is owed in, one either side of a line.
     *
     * <p>Subject: the position. Raised by a rule that treats the two sides of a line differently
     * and leaves values on both — which is what a class is. A {@code guard}'s comparison is one, and
     * so is a clause of an {@code ensures} about an input; an invariant's bound is not, because
     * everything outside it is refused at construction and there is no class on the far side
     * (ADR-0090). That is a fact about the construct the rule is written in and not about the
     * comparison, which is why the two are asked separately where a rule raises this.
     *
     * <p>Beside {@link #BOUNDARY} and never instead of it. One line, two questions: which rows are
     * owed at the line, and which rows are owed either side of it. A rule that draws a line raises
     * both, and a measure counting one for the other reports a model divided where nothing said so.
     */
    PARTITION
}
