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

        assertFalse(filling.pairs().rows().isEmpty(), "there are rows to offer");
        assertEquals(List.of(), unconfirmed(filling),
                "and each was run and seen reaching what it is offered for");
    }

    @Test
    void aBuildThatDoesNotMeasureTheArmsSaysItsRowsWereNotRun() {
        Adequacy.Filling filling = generationOf(Adequacy.Level.WITNESS);

        assertFalse(filling.pairs().rows().isEmpty(),
                "the rows are still offered, being worth writing either way");
        assertEquals(1, unconfirmed(filling).size(),
                "and the generation says once that nothing ran them: " + filling.pairs().reasons());
    }

    private static List<GenerationReason> unconfirmed(Adequacy.Filling filling) {
        return filling.pairs().reasons().stream()
                .filter(GenerationReason.RowsNotConfirmed.class::isInstance).toList();
    }

    private static Adequacy.Filling generationOf(Adequacy.Level level) {
        Compilation compilation = Compilation.ofSource(SHIPPING, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(level));
        compilation.answerEverything();
        Map<String, Adequacy.Filling> filled = compilation.db()
                .ask(new Adequacy.Generated(compilation.modules().get(0))).value();
        assertNotNull(filled, "the model under test compiles and is measured");
        Adequacy.Filling filling = filled.get("shippingFee");
        assertNotNull(filling, "the behavior under test was generated for");
        assertTrue(filling.pairs().unresolved().stream().noneMatch(each -> each.reason()
                        == souther.compiler.partition.Generator.UnresolvedCombination.Reason
                                .NO_CERTIFIED_WITNESS),
                "nothing missed: " + filling.pairs().unresolved());
        return filling;
    }
}
