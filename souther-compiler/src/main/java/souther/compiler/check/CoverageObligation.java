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
 *
 * <p><b>And not every coverage target.</b> What rows a model owes and what questions stand until
 * something answers them are two sets, and only the second is here. A comparison this compiler can
 * read owes rows — at the value it singles out, in the classes its line makes — and owes them by
 * having been read: the reading that finds the line is what asks for them, so there is no moment at
 * which such a demand is outstanding. Those live where the partition's geometry does. Held here as
 * well, they were raised and answered in one breath and the two sets came apart nowhere except in
 * the name.
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
     * <p>Subject: where the line falls, which is the number the position is measured at. Raised by a
     * clause of a declaration that places an end on one of its value's positions.
     *
     * <p>Not by a comparison. A body's condition and a clause of an {@code ensures} draw lines too,
     * and what they owe is owed by having been read — the reading that finds the line is what asks
     * for the rows either side, so no such demand is ever outstanding. Those live where the
     * partition's geometry does.
     */
    BOUNDARY;


    /**
     * Which measure of coverage answers this question.
     *
     * <p>Settled here, where the question is, and read by everything that has to know. A report
     * chooses which section to print a standing question under, and a measure has to know which
     * questions it is short of before it may say it read the model — two readings of one table, and
     * the table was a renderer's private method while the second reader did not exist. Written
     * twice, the day a question is added is the day one of them files it somewhere and the other
     * silently answers for it.
     *
     */
    public Measure answeredBy() {
        return switch (this) {
            case ADMITTED_VALUES -> Measure.PARTITION;
            case BOUNDARY -> Measure.BOUNDARY;
        };
    }

    /**
     * A measure of coverage, as the questions are filed under it.
     *
     * <p>Two, and each answers for itself. What one of them is short of says nothing about the
     * other: a rule whose line nothing could read leaves the border measure short while the classes
     * either side of it were read in full, and a completeness shared between the two would report
     * both on the strength of whichever failed.
     */
    public enum Measure {

        /** Which values may stand where, which classes hold them, and which value is singled out. */
        PARTITION,

        /** Where a line falls, and the rows either side of it. */
        BOUNDARY
    }
}
