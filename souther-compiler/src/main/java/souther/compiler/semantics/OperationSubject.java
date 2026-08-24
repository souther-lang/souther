package souther.compiler.semantics;

/**
 * What there is to say about one of the language's operations.
 *
 * <p>The subjects, and not the questions a procedure asks. Which of these a given check consults is
 * that check's business; that an operation either keeps the elements of what it was built from or
 * keeps nothing of them is true whether or not anything asks.
 *
 * <p>Here because a fact and its absence are about the same subject. An operation says something
 * under one of these or is declared to say nothing under it, with the reason
 * ({@link OperationFact.SaysNothingOf}) — and a silence that is a decision has to be told from one
 * that is a gap. Held beside the questions instead, the two enumerations would be kept in step by
 * whoever remembered.
 */
public enum OperationSubject {

    COMBINATOR("what it hands its closure"),
    REDUCTION("whether it reduces a container from a seed through its closure"),
    ACCUMULATION("whether it accumulates what its container holds, and from what through what"),
    BUILT("what it keeps of the container it is built from"),
    PREDICATE_CARRY("where the predicate it states reads its container, and how far that travels"),
    EMPTINESS("which size call it means"),
    QUANTIFICATION("whether it states its predicate of every element"),
    PROJECTION("which argument is the projection it is stated over"),
    SIZE("whether the number it answers is a size"),
    ORDER("whether it answers the order of its two arguments"),
    BOUNDS("what bounds the number it answers"),
    MEASURE("what it states through the measure counting the two apart"),
    CHOICE("whether it answers one of its arguments, and in which cases"),
    FORM("what it answers, counted, in what its arguments are counted as"),
    NUMERIC_RESULT("what number it computes, and where it answers it");

    private final String asked;

    OperationSubject(String asked) {
        this.asked = asked;
    }

    /** What is being said of the operation, for a message that names it. */
    public String asked() {
        return asked;
    }
}
