package souther.compiler.report;

/**
 * What a reader is told where the model settles that no value stands somewhere.
 *
 * <p>One place for the words, so every sentence a proof is said in makes the same claim and none
 * of them says what proved it. A type with few values, a rule on the type, a rule on a container's
 * size and how many of an element's values meet a statement each settle it, two of them may settle
 * one point alike, and a reader does the same about the point whichever did. A sentence naming the
 * rules would send an author looking for a rule that a {@code Set<Bool>} asked for three values does
 * not have.
 *
 * <p>A sentence that does not say a proof does not say {@link #CAN} either: a search that stopped
 * or composed nothing settles nothing, and said in these words it would read as though it had.
 */
final class NoValue {

    /** The claim every sentence here makes, and no sentence about anything short of a proof. */
    static final String CAN = "no value can";

    private NoValue() {}

    /** No value can stand at {@code where}. */
    static String standsAt(String where) {
        return CAN + " stand at " + where;
    }

    /** No value can stand at the point the sentence is about. */
    static String standsThere() {
        return CAN + " stand there";
    }

    /** No value can stand at what the line is written under. */
    static String standsHere() {
        return CAN + " stand here";
    }

    /** No value can go the way the sentence is about. */
    static String goesThatWay() {
        return CAN + " go that way";
    }

    /** No value can reach {@code what}. */
    static String reaches(String what) {
        return CAN + " reach " + what;
    }
}
