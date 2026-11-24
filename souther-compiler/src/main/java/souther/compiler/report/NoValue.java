package souther.compiler.report;

import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.ReportMessage;

/**
 * What a reader is told where the model settles that no value stands somewhere.
 *
 * <p>One place for the claim, so every sentence a proof is said in makes the same claim and none
 * of them says what proved it. A type with few values, a rule on the type, a rule on a container's
 * size and how many of an element's values meet a statement each settle it, two of them may settle
 * one point alike, and a reader does the same about the point whichever did. A sentence naming the
 * rules would send an author looking for a rule that a {@code Set<Bool>} asked for three values does
 * not have.
 *
 * <p>Each claim is a message, carried whole by the sentence that makes it, so the claim reads alike
 * in every sentence of every language. A sentence that does not say a proof does not carry one of
 * these: a search that stopped or composed nothing settles nothing, and said in these words it would
 * read as though it had.
 */
final class NoValue {

    /** How every one of these claims opens in the base catalog, which is how a reader of the
     *  base language tells a proof from a search that stopped. */
    static final String CAN = "no value can";

    private NoValue() {}

    /** No value can stand at {@code where}. */
    static Message standsAt(String where) {
        return new ReportMessage.NoValueCanStandAt(where);
    }

    /** No value can stand at what the sentence names just before. */
    static Message standsAtIt() {
        return new ReportMessage.NoValueCanStandAtIt();
    }

    /** No value can stand at the point the sentence is about. */
    static Message standsThere() {
        return new ReportMessage.NoValueCanStandThere();
    }

    /** No value can stand at what the line is written under. */
    static Message standsHere() {
        return new ReportMessage.NoValueCanStandHere();
    }

    /** No value can go the way the sentence is about. */
    static Message goesThatWay() {
        return new ReportMessage.NoValueCanGoThatWay();
    }

    /** No value can reach the arm the sentence is about. */
    static Message reachesThatArm() {
        return new ReportMessage.NoValueCanReachThatArm();
    }

    /** No value can reach what the sentence is about coming out the way it says. */
    static Message reachesItComingOutSo() {
        return new ReportMessage.NoValueCanReachItComingOutSo();
    }
}
