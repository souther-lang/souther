package souther.bench;

import org.junit.jupiter.api.Test;

import souther.compiler.publish.PublicationOrders;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field a document decides the order of is written from a sequence somebody put in order.
 *
 * <p>What the orders themselves cannot say. A method that starts an array and walks a collection
 * into it publishes whatever that collection iterates in, and there is nothing in the array or in
 * the collection to say so — the document comes out looking the same until something upstream is
 * tidied, and then it comes out different for a reason no diff explains.
 *
 * <p><b>Which fields, read off what was declared and not off the schema.</b> Whether an array's
 * order is this compiler's or the model's is a fact about the contract rather than about the shape
 * of the field, so it is written down where the orders are
 * ({@link PublicationOrders#CANONICALLY_ARRANGED_FIELDS}). Read off the schema instead, this would
 * be asking every array of the document to be sorted, which is false of the ones whose order is the
 * order somebody wrote — and a check making that demand would be met by sorting them.
 *
 * <p>So the arrays whose order is somebody's own are outside this on purpose, and
 * {@link #anArrayWhoseOrderIsNotThisCompilersIsOutsideThis} is what says the population really does
 * leave them out rather than happening to contain no counterexample.
 */
class AFieldWhoseOrderIsThisCompilersIsWrittenThroughACrossingTest {

    private static final String STARTS_AN_ARRAY = "putArray";

    private static final Set<String> CROSSINGS = Set.of(
            "souther.compiler.publish.CanonicalArrangement",
            "souther.compiler.publish.CanonicalSelection",
            "souther.compiler.publish.SourceOrdered");

    @Test
    void everyFieldWhoseOrderIsThisCompilersIsWrittenFromACrossing() throws Exception {
        List<String> straightFromACollection = new ArrayList<>();
        for (String field : PublicationOrders.CANONICALLY_ARRANGED_FIELDS) {
            Set<String> writers = whereTheArrayIsStarted(field);
            assertFalse(writers.isEmpty(), () -> "nothing writes " + field + ", so what this holds"
                    + " to that name is nothing");
            for (String writer : writers) {
                // The method and no more of it. What is read here is that a method reaches a
                // crossing, so a method that also writes an array with an order of its own would
                // answer for that one by having crossed for this.
                Set<String> alsoStartedThere = arraysStartedIn(writer);
                if (!alsoStartedThere.equals(Set.of(field))) {
                    straightFromACollection.add(field + " is written by " + writer
                            + ", which also writes " + alsoStartedThere);
                } else if (!crossesIn(writer)) {
                    straightFromACollection.add(field + " is written by " + writer
                            + ", which reaches no crossing");
                }
            }
        }

        assertEquals(List.of(), straightFromACollection,
                "a field whose order this compiler decides is written straight out of a collection,"
                        + " so what a reader is given is whatever that iterates in");
    }

    /**
     * And a field whose order is somebody else's is not asked to go through one.
     *
     * <p>The control. Without it this passes by holding two fields to a rule and saying nothing
     * about whether the rule was written wide enough to be false of anything — and the way this
     * check goes wrong is by growing until it demands an order of arrays that have one.
     */
    @Test
    void anArrayWhoseOrderIsNotThisCompilersIsOutsideThis() throws Exception {
        Set<String> writers = whereTheArrayIsStarted("behaviors");

        assertFalse(writers.isEmpty(), "nothing writes the behaviors of a module");
        assertTrue(writers.stream().noneMatch(
                        AFieldWhoseOrderIsThisCompilersIsWrittenThroughACrossingTest::crossesIn),
                () -> "the behaviors of a module are written in the order they were declared in,"
                        + " and something is now putting them in an order of this compiler's:"
                        + " " + writers);
        assertFalse(PublicationOrders.CANONICALLY_ARRANGED_FIELDS.contains("behaviors"),
                "a field written in the order somebody wrote it is not one this compiler orders");
    }

    /** Every array {@code method} starts, so that a method answering for one is answering for
     *  nothing else. */
    private static Set<String> arraysStartedIn(String method) throws Exception {
        Set<String> out = new LinkedHashSet<>();
        for (Compiled.Invocation each : Compiled.invocations()) {
            if (each.site().at().equals(method) && each.site().member().equals(STARTS_AN_ARRAY)) {
                out.addAll(each.said());
            }
        }
        return out;
    }

    /** The methods that start an array under {@code field}, read off the name written at the call. */
    private static Set<String> whereTheArrayIsStarted(String field) throws Exception {
        Set<String> out = new LinkedHashSet<>();
        for (Compiled.Invocation each : Compiled.invocations()) {
            if (each.site().member().equals(STARTS_AN_ARRAY) && each.said().contains(field)) {
                out.add(each.site().at());
            }
        }
        return out;
    }

    /** Whether that method takes what it writes from a sequence somebody put in order. */
    private static boolean crossesIn(String method) {
        try {
            for (Compiled.Site site : Compiled.sites()) {
                if (site.at().equals(method) && CROSSINGS.contains(site.owner())
                        && site.member().equals("written")) {
                    return true;
                }
            }
            return false;
        } catch (Exception opaque) {
            throw new AssertionError("the compiled classes could not be read", opaque);
        }
    }
}
