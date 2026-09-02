package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nothing reads what a module could not read except as the sequence it is published as.
 *
 * <p>Beside the check over the document's repeated fields, and asking the other half. That one is
 * about a field of the document and says a writer of it goes through a crossing; this is about the
 * facts, and says the same of every surface — because there are three, and putting an order on the
 * one that has a schema is what left the other two saying whatever a set iterated in.
 *
 * <p><b>Read as who may reach the account.</b> What holds these facts is a set with no order, and
 * the way a surface comes to publish them out of order is by holding one. So the rule is over who
 * may ask for it: the account answers with a set, one place turns that into the sequence a document
 * writes, and no surface asks the account itself.
 *
 * <p>Which is stronger than asking each surface to cross. A surface that has no set cannot publish
 * one in the wrong order, and a surface added later is inside this without anybody adding a line.
 */
class EverySurfaceThatSaysWhatWentUnreadTakesOneSequenceTest {

    private static final String THE_ACCOUNT = "souther.compiler.query.WeakeningSet";
    private static final String THE_FACTS = "observationCauses";

    /** The one place a set of these becomes the sequence a document writes. */
    private static final String THE_CROSSING =
            "souther.compiler.publish.PublishedIncompleteness#everyOne";

    /**
     * What is allowed to ask the account for them: the crossing, and the report's own answer for
     * one module, which is that crossing's result and nothing else.
     */
    private static final Set<String> MAY_ASK = Set.of(
            "souther.compiler.publish.PublishedIncompleteness",
            "souther.compiler.report.AdequacyReport$ModuleReport",
            // A reading's own account of what it went without, which is not a surface: what a
            // measure does with these is ask which of them bear on it, and a measure publishes
            // nothing. Where one of these is published — the block a generator writes — it goes
            // through the crossing like the others.
            "souther.compiler.query.Adequacy$RowReading");

    @Test
    void nothingButTheCrossingAsksTheAccountForTheFacts() throws Exception {
        List<String> asking = new ArrayList<>();
        boolean reached = false;
        for (Compiled.Site site : Compiled.sites()) {
            if (!site.owner().equals(THE_ACCOUNT) || !site.member().equals(THE_FACTS)) {
                continue;
            }
            reached = true;
            String from = site.at().substring(0, site.at().indexOf('#'));
            if (!MAY_ASK.contains(from)) {
                asking.add(site.at());
            }
        }

        assertTrue(reached, "nothing asks the account what it went without, so this holds nothing");
        assertEquals(List.of(), asking,
                "something takes the facts a module could not read out of the account itself,"
                        + " which is a set — so what it publishes is in whatever that iterates in");
    }

    /**
     * And every surface that says them takes the sequence from that one crossing.
     *
     * <p>Named as the surfaces there are rather than derived, because what counts as one is a
     * question about the product: a page, a document, a generated block. What is derived is who
     * reaches the crossing, so a surface here that stopped using it is caught.
     */
    @Test
    void everySurfaceThatSaysThemReachesTheCrossing() throws Exception {
        Set<String> reaching = new LinkedHashSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (site.at().startsWith(THE_CROSSING)) {
                continue;
            }
            if ((site.owner() + "#" + site.member()).equals(THE_CROSSING)) {
                reaching.add(site.at().substring(0, site.at().indexOf('#')));
            }
        }

        assertEquals(Set.of("souther.compiler.report.AdequacyReport$ModuleReport",
                        "souther.compiler.report.GeneratedRows"),
                reaching,
                "what reaches the crossing is not what says these facts: the page and the document"
                        + " are both written from the report's answer for one module, and the"
                        + " generated block asks for itself");
    }
}
