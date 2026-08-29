package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comparison read from end to end says which positions it is about, and says it itself.
 *
 * <p>A rule whose quantity cancels is read in full and divides nothing: {@code a - a <= 0} holds of
 * every row, and a report that stayed silent about it would leave the position looking like one the
 * model states nothing at. What it is about is therefore said — and what it is about is what the
 * reading named on the way, not what is left of the quantity, since what is left is nothing.
 *
 * <p>Which is why the walk over the operands is not asked. That walk is what a rule the reading could
 * not finish is described by; asked about one the reading finished, it is a second account of the
 * same thing and a stricter one — two values that are one form written two ways are made of
 * different things — so a rule read in full would go out as one about no input at all, which is
 * neither a line nor a shortfall.
 */
class ARuleReadToTheEndSaysWhatItIsAboutTest {

    /** The rule is recorded at the position it names, and its quantity is empty. */
    private static final String CUTS_NOTHING_AT_N = "[] unread [n RULE_CUTS_NOTHING]";

    /** Members that write one form two ways cancel against each other and name the position. */
    @Test
    void membersWritingOneFormTwoWaysStillNameThePosition() {
        assertEquals(CUTS_NOTHING_AT_N, reading("""
                {
                        let ks = [ Big { threshold = n + n }, Big { threshold = 2 * n } ]
                        if List.any((k) -> k.threshold <= k.threshold, ks) then Yes else No
                    }"""));
    }

    /**
     * And so do members that write it one way.
     *
     * <p>Beside the one above and differing in nothing the model states. Two spellings of one form
     * are one rule, and a reader that told them apart would be reporting how a list was written.
     */
    @Test
    void membersWritingItOneWayNameTheSamePosition() {
        assertEquals(CUTS_NOTHING_AT_N, reading("""
                {
                        let ks = [ Big { threshold = n + n }, Big { threshold = n + n } ]
                        if List.any((k) -> k.threshold <= k.threshold, ks) then Yes else No
                    }"""));
    }

    /**
     * A quantity that cancels inside one side names its position too.
     *
     * <p>No plurality anywhere here, and it is what says the coordinates cannot come off the form
     * the reading ended with: that form has no atom in it, and the rule is about {@code n} all the
     * same.
     */
    @Test
    void aQuantityCancellingInsideOneSideNamesItsPosition() {
        assertEquals(CUTS_NOTHING_AT_N, reading("if n - n <= 0 then Yes else No"));
    }

    /**
     * A number taken of a position is filed as that number and not as the position.
     *
     * <p>What the reading named is the length, and a rule about the length is not a rule about the
     * string: two operations over one place are two rules, and a report that filed both at the place
     * would have them as one. The reading reached the number, so the number is what it says — a
     * coordinate that names only the place is for a reader that did not get that far.
     */
    @Test
    void aNumberTakenOfAPositionIsFiledAsThatNumber() {
        assertEquals("[] unread [String.length(s) RULE_CUTS_NOTHING]", reading(
                "if String.length(s) - String.length(s) <= 0 then Yes else No"));
    }

    /**
     * A comparison of constants names nothing, and nothing is recorded.
     *
     * <p>The other side of the same rule. It is read from end to end and cuts nothing, and there is
     * no position for a sentence about one to be about — so what tells this from the three above is
     * that the reading named no number, and not that its quantity is empty.
     */
    @Test
    void aComparisonOfConstantsIsAboutNoPosition() {
        assertEquals("[] unread []", reading("if 2 > 1 then Yes else No"));
    }

    private static String reading(String body) {
        return MeasuredBehavior.reading("""
                module g

                data Big = { threshold: Int }
                data Yes
                data No

                behavior classify : (n: Int, s: String) -> Yes | No
                let classify (n, s) = %s

                example classify
                    | "one" : (1, "") -> Yes
                """.formatted(body), "classify");
    }
}
