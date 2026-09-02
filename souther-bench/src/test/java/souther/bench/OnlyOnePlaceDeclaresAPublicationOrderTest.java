package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Who may say what order a plurality of reasons is in.
 *
 * <p>Two orders and two answers, and the asymmetry between them is the arrangement. What order this
 * compiler publishes a kind in is one decision for the whole compiler, so making one is closed to
 * the place that declares them. That a particular sequence is in the order the model has is not a
 * decision at all — it is something a producer either knows or does not — so anybody who knows it
 * may say it, and a reader who does not may not.
 *
 * <p>Read off the call sites rather than off the declarations. A check over the fields of the
 * classes there would see a field of the order's type and miss an order made inside a method and
 * used from there, which is the same second order with nowhere to see it. What makes one of these
 * is calling a method, and this says who calls them.
 */
class OnlyOnePlaceDeclaresAPublicationOrderTest {

    private static final String ORDER = "souther.compiler.publish.CanonicalSelection$Order";
    private static final String ARRANGEMENT =
            "souther.compiler.publish.CanonicalArrangement$Order";
    private static final String AUTHORITY = "souther.compiler.publish.PublicationOrders";
    private static final String SOURCE_ORDERED = "souther.compiler.publish.SourceOrdered";
    private static final String REPORT = "souther.compiler.report.";

    @Test
    void nothingButThePublicationOrdersMakesAnOrder() throws Exception {
        List<String> made = new ArrayList<>();
        boolean reached = false;
        for (Compiled.Site site : Compiled.sites()) {
            if ((site.owner().equals(ORDER)
                        && (site.member().equals("overValues")
                                || site.member().equals("overFamilies")))
                    // And the other shape an order comes in. A sequence whose length is not bounded
                    // by a vocabulary is put in order by a comparison rather than by a list of
                    // places, and a second one of those is a second decision about what a reader is
                    // shown just as readily.
                    // Called or named for later, because either makes one: a reference runs the
                    // same factory somewhere else and puts no invoke in the caller's code, so a
                    // rule counting calls alone is passed by `Order::by`. What is not making one
                    // is reading the field the comparison is held in, which has the same name.
                    || (site.owner().equals(ARRANGEMENT) && site.member().equals("by")
                            && (site.how() == Compiled.How.CALLS
                                    || site.how() == Compiled.How.REFERS))) {
                reached = true;
                if (!site.from().equals(AUTHORITY)) {
                    made.add(site.at());
                }
            }
        }

        assertFalse(made.isEmpty() && !reached,
                "no order is made anywhere, so this is passing for the wrong reason");
        assertEquals(List.of(), made,
                "an order over a kind of reason made outside the one place that declares them,"
                        + " which is how a kind comes to have two orders that agree until one moves");
    }

    /**
     * A report says of no sequence that its order is the model's.
     *
     * <p>The claim a {@link souther.compiler.publish.SourceOrdered} carries is that the order came
     * from what somebody wrote, and by the time a plurality is at a report nothing left in it says
     * where its order came from. Made there, the type would be a report calling whatever it was
     * handed the author's order — which is the check that a plurality arrives having been answered
     * for, passed by answering for it at the end.
     */
    @Test
    void aReportSaysOfNoSequenceThatItsOrderIsTheModelsOwn() throws Exception {
        List<String> claimed = new ArrayList<>();
        boolean reached = false;
        for (Compiled.Site site : Compiled.sites()) {
            if (site.owner().equals(SOURCE_ORDERED) && site.member().equals("asWritten")) {
                reached = true;
                if (site.from().startsWith(REPORT)) {
                    claimed.add(site.at());
                }
            }
        }

        assertFalse(claimed.isEmpty() && !reached,
                "nothing anywhere says a sequence is in the order it was written, so this is"
                        + " passing for the wrong reason");
        assertEquals(List.of(), claimed,
                "a report claims the model's order for a sequence it was handed, which is a claim"
                        + " about something it cannot see");
    }
}
