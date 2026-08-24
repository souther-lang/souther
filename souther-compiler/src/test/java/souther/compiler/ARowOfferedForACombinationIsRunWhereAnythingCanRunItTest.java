package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.GenerationReason;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a build confirms the rows it offers, and what it says where it cannot.
 *
 * <p>What confirms one is running it, and running one records where it went only in classes emitted
 * with the calls that record it. A build that does not measure the arms has no such classes, so its
 * rows are offered on the strength of a reading of the body and it says so. A build that does has
 * them, and every row it offers for a combination is one that was seen reaching it.
 *
 * <p>The two are asserted together because either alone would pass on a mistake. Confirming nothing
 * would leave the first true and the second silent; confirming against classes with no calls in them
 * would leave every candidate missing, offer nothing, and leave the second true by having no rows to
 * be unconfirmed about.
 */
class ARowOfferedForACombinationIsRunWhereAnythingCanRunItTest {

    /** Two decisions consumed into one value, and no row written for any of their combinations. */
    private static final String SHIPPING = """
            module example.shipping

            data Membership = Premium | Standard

            data Delivery = Express | Regular

            data Fee = Int
                invariant value >= 0

            behavior shippingFee : (member: Membership, delivery: Delivery) -> Fee
                constructs Fee

            let baseFee (tier: Membership): Int =
                match tier with
                    | Premium -> 0
                    | Standard -> 500

            let expressFee (speed: Delivery): Int =
                match speed with
                    | Express -> 500
                    | Regular -> 0

            let shippingFee (member, delivery) =
                Fee(baseFee(member) + expressFee(delivery))
            """;

    @Test
    void aBuildThatMeasuresTheArmsConfirmsTheRowsItOffers() {
        Adequacy.Filling filling = generationOf(Adequacy.Level.ALL);

        assertFalse(filling.composed().rows().isEmpty(), "there are rows to offer");
        assertEquals(List.of(), unconfirmed(filling),
                "and each was run and seen reaching what it is offered for");
    }

    /**
     * A build that does not measure the arms is owed no row at one, and offers none.
     *
     * <p>This used to offer them anyway and say that nothing had run them. That was the search
     * having a list of its own: a combination is where a row through an arm is looked for, and
     * which arms are owed one is what measuring them establishes. A build that measured none has
     * established nothing, and a row offered for an arm on the strength of a measurement nobody
     * made is work handed over on nobody's word — which is what a position held back over an
     * unreadable value already says (`PositionWithheld`).
     *
     * <p>The classes are unaffected: what they divide into is read off the model and needs no
     * second run, so what is owed there does not turn on the level.
     */
    @Test
    void aBuildThatDoesNotMeasureTheArmsIsOwedNoRowAtOne() {
        Adequacy.Filling filling = generationOf(Adequacy.Level.WITNESS);

        assertFalse(filling.composed().rows().isEmpty(), "the classes are still offered");
        assertEquals(List.of(), filling.composed().rows().stream()
                        .flatMap(row -> row.purposes().stream())
                        .filter(souther.compiler.partition.Generator.Purpose.ForAnArm.class
                                ::isInstance)
                        .toList(),
                "and no row is composed for an arm, none being owed one");
        assertEquals(List.of(), unconfirmed(filling),
                "so there is nothing to say went unrun");
    }

    /** The same two decisions, in a behavior that depends on another. */
    private static final String DEPENDING = """
            module example.postage

            data Membership = Premium | Standard

            data Delivery = Express | Regular

            data Fee = Int
                invariant value >= 0

            behavior surcharge : (member: Membership) -> Fee

            behavior postageFor : (member: Membership, delivery: Delivery) -> Fee
                constructs Fee
                depends on surcharge

            let expressFee (speed: Delivery): Int =
                match speed with
                    | Express -> 500
                    | Regular -> 0

            let baseFee (tier: Membership): Int =
                match tier with
                    | Premium -> 0
                    | Standard -> 500

            let postageFor (member, delivery, surcharge) =
                Fee(baseFee(member) + expressFee(delivery) + surcharge(member).value)
            """;

    /**
     * A behavior nothing can apply for a composed row is unconfirmed, not missed.
     *
     * <p>A row composed here names no fakes, so a behavior that depends on another has nothing to
     * stand in for what it depends on and cannot be applied at all. Read as a run, that is a row
     * which reached nothing — and every combination would come back as one every candidate missed,
     * which says the search found something out about the model. It found nothing out.
     */
    @Test
    void aBehaviorNothingCanApplyIsOwedNoRowAtAnArm() {
        Adequacy.Filling filling = generationOf(DEPENDING, "postageFor", Adequacy.Level.ALL);

        assertFalse(filling.composed().rows().isEmpty(), "the classes are still offered");
        assertEquals(List.of(), filling.composed().rows().stream()
                        .flatMap(row -> row.purposes().stream())
                        .filter(souther.compiler.partition.Generator.Purpose.ForAnArm.class
                                ::isInstance)
                        .toList(),
                "and none for a combination: nothing applied the rows, so no arm is established"
                        + " unreached");
    }

    /** The shipping model with two of its four combinations already written. */
    private static final String WRITTEN = SHIPPING + """

            example shippingFee
                | (Premium, Express) -> Fee(500)
                | (Standard, Regular) -> Fee(500)
            """;


    /**
     * A row the author already wrote is not offered back to them because nothing watched it.
     *
     * <p>Where nothing can say what a row did, the two kinds of row part. An author's row is in the
     * file whatever this establishes about it, so passing over a combination it may fill costs a
     * combination left owed; offering one costs them work they have already done. A row this search
     * composed is in nobody's file and gets no such benefit.
     */
    @Test
    void aWrittenRowIsNotOfferedBackWhereNothingCouldWatchIt() {
        assertEquals(offeredBy(Adequacy.Level.ALL), offeredBy(Adequacy.Level.WITNESS),
                "what is left to write does not turn on whether the build was measuring");
    }

    /**
     * Nothing is held back over a combination, nobody being owed one.
     *
     * <p>This used to count the combinations a written row might have filled and say how many, so
     * that silence did not read as coverage. What made the count necessary was the search treating
     * a combination as a thing owed a row: it could neither offer one over a row that might already
     * fill it nor pass over it in silence. Neither question arises now — an arm is owed a row only
     * where the measure established that no row reaches it, and a row that might have is a row that
     * was read.
     */
    @Test
    void nothingIsHeldBackOverACombination() {
        for (Adequacy.Level level : List.of(Adequacy.Level.WITNESS, Adequacy.Level.ALL)) {
            assertEquals(List.of(),
                    generationOf(WRITTEN, "shippingFee", level).composed().reasons().stream()
                            .filter(GenerationReason.SearchLimit.class::isInstance).toList(),
                    level::name);
        }
    }

    private static List<List<String>> offeredBy(Adequacy.Level level) {
        return generationOf(WRITTEN, "shippingFee", level).composed().rows().stream()
                .map(souther.compiler.partition.Generator.GeneratedRow::labels).toList();
    }

    private static List<GenerationReason> unconfirmed(Adequacy.Filling filling) {
        return filling.composed().reasons().stream()
                .filter(GenerationReason.RowsNotConfirmed.class::isInstance).toList();
    }

    private static Adequacy.Filling generationOf(Adequacy.Level level) {
        return generationOf(SHIPPING, "shippingFee", level);
    }

    private static Adequacy.Filling generationOf(String source, String behavior,
                                                 Adequacy.Level level) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(level));
        compilation.answerEverything();
        Map<String, Adequacy.Filling> filled = Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(filled, "the model under test compiles and is measured");
        Adequacy.Filling filling = filled.get(behavior);
        assertNotNull(filling, "the behavior under test was generated for");
        assertTrue(filling.composed().unresolved().stream().noneMatch(each -> each.reason()
                        == souther.compiler.partition.Generator.UnresolvedCombination.Reason
                                .NO_CERTIFIED_WITNESS),
                "nothing missed: " + filling.composed().unresolved());
        return filling;
    }
}
