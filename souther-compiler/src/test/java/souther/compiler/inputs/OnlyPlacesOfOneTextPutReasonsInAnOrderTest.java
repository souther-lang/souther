package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourcePos;
import souther.compiler.source.SourceId;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Which order a question's rule-side reasons are in, and whether it is one anybody wrote.
 *
 * <p>The rule itself, asked of the one place that answers it. What reaches a document is words, and
 * a word cannot be asked where it was written — so what a reader may do with the order is settled
 * here, out of the places, and everything downstream carries the answer rather than making one.
 */
class OnlyPlacesOfOneTextPutReasonsInAnOrderTest {

    private static final SourceId ONE = new SourceId("one");

    private static final SourceId ANOTHER = new SourceId("another");

    private static final BlockReason.RuleReadingStopped FORM =
            new BlockReason.UnreadComparisonForm();

    private static final BlockReason.RuleReadingStopped DOMAIN =
            new BlockReason.UnreadComparisonDomain();

    /**
     * Sorted by the place before folded on the reason, and never the other way round.
     *
     * <p>What the fold keeps is the first entry, so which entry that is turns on what came first —
     * the earliest place the reason stands on, or whichever copy of it the walk met. Folded first,
     * a reason standing at two places keeps the one that was met, and a reason written before it
     * comes out after it.
     */
    @Test
    void aReasonStandingTwiceIsSaidWhereItWasFirstWritten() {
        assertEquals(List.of(FORM, DOMAIN),
                RuleReasons.from(List.of(
                        new RuleReasons.Placed(at(30), FORM),
                        new RuleReasons.Placed(at(10), DOMAIN),
                        new RuleReasons.Placed(at(5), FORM))).reasons(),
                "the form is written before the domain and is said before it, however late the"
                        + " copy of it that was met first stands");
    }

    /** And two reasons at one place are put in the order the vocabulary declares them in. */
    @Test
    void twoReasonsAtOnePlaceArePutInTheOrderTheVocabularyDeclares() {
        assertEquals(RuleReasons.from(List.of(
                        new RuleReasons.Placed(at(1), FORM),
                        new RuleReasons.Placed(at(1), DOMAIN))).reasons(),
                RuleReasons.from(List.of(
                        new RuleReasons.Placed(at(1), DOMAIN),
                        new RuleReasons.Placed(at(1), FORM))).reasons(),
                "nothing an author wrote tells them apart, so nothing about how they were met may"
                        + " decide it either");
    }

    /** Reasons of one text stand in an order somebody wrote. */
    @Test
    void reasonsOfOneTextStandInAnOrderSomebodyWrote() {
        assertInstanceOf(RuleReasons.AsWritten.class,
                RuleReasons.from(List.of(
                        new RuleReasons.Placed(at(5), FORM),
                        new RuleReasons.Placed(at(10), DOMAIN))));
    }

    /**
     * And reasons of two texts stand in no order anybody wrote.
     *
     * <p>A line and a column are a place within one text and two numbers outside it. Line 5 of two
     * files is the same pair and is not the same place, so an order taken over the numbers alone
     * would put a reason of one file before a reason of another for no reason at all.
     */
    @Test
    void andReasonsOfTwoTextsStandInNoOrderAnybodyWrote() {
        assertInstanceOf(RuleReasons.NoSingleAuthoredOrder.class,
                RuleReasons.from(List.of(
                        new RuleReasons.Placed(new SourcePos(5, 1, ONE), FORM),
                        new RuleReasons.Placed(new SourcePos(10, 1, ANOTHER), DOMAIN))),
                "nothing an author did says which file comes first");
    }

    /** And one reason is in an order somebody wrote by there being nothing to order it against. */
    @Test
    void oneReasonIsAnOrderSomebodyWrote() {
        assertInstanceOf(RuleReasons.AsWritten.class, RuleReasons.one(FORM));
        assertEquals(List.of(FORM), RuleReasons.one(FORM).reasons());
    }

    /** A place in the one text these are written in. */
    private static SourcePos at(int column) {
        return new SourcePos(1, column, ONE);
    }
}
