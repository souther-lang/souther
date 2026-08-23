package souther.bench;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reader that tells one way of deciding an arm from another switches over all of them, and none
 * asks after the one it knows.
 *
 * <p>What decides an arm of a choice is a sum ({@code Choice.Decides}), and it is a sum so that a
 * way of deciding added later stops every reader that interprets one until somebody has said what it
 * means there. An exhaustive {@code switch} carries that: it stops at compile time. The same reader
 * written as an {@code instanceof} does not — it compiles unchanged and answers about the arms it
 * knew, silently, in whichever direction its {@code else} went.
 *
 * <p>Which is not hypothetical. What choosing an arm settles was written that way, and the arms it
 * did not name were left answering "nothing is settled" — so a choice whose arms were read and whose
 * conditions were dropped would have been bounded by a span over values it cannot take, with nothing
 * anywhere saying a reader had been missed. The compiler cannot refuse that, since asking is legal
 * Java; this is what refuses it.
 *
 * <p>Read off the bytecode, where the difference is visible: an exhaustive switch over a sealed type
 * is one {@code invokedynamic} and an {@code instanceof} is its own instruction ({@link Compiled}).
 */
class AWayOfDecidingAnArmIsToldApartBySwitchingOverThemAllTest {

    private static final String DECIDES = "souther.compiler.check.Choice$Decides";

    @Test
    void nobodyAsksWhetherAnArmWasDecidedTheOneWayItKnows() throws IOException {
        Set<String> asking = new LinkedHashSet<>();
        Set<String> reached = new LinkedHashSet<>();
        boolean anyAskAtAll = false;
        for (Compiled.Site site : Compiled.sites()) {
            anyAskAtAll |= site.how() == Compiled.How.ASKS;
            if (!site.owner().startsWith(DECIDES)) {
                continue;
            }
            reached.add(site.from());
            if (site.how() == Compiled.How.ASKS) {
                asking.add(site.at());
            }
        }
        assertTrue(anyAskAtAll,
                "no class anywhere was seen asking a type of a value, so this check cannot tell one"
                        + " that does from one that does not");
        assertTrue(reached.size() > 1,
                "a way of deciding an arm was reached from " + reached + ", which is too few for"
                        + " this to be about the readers it is written for");
        assertEquals(Set.of(), asking,
                "a reader asks after one way of deciding an arm instead of switching over them all."
                        + " Written that way it answers for the ways it was told about and passes"
                        + " the rest through, which is the silence a sum exists to turn into a"
                        + " compile error");
    }
}
