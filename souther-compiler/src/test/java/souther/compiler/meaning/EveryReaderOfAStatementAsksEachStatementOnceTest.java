package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.ReadersOfAGraph;
import souther.compiler.inputs.TermPath;
import souther.test.ClosedWorldContract;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every reader of a statement asks each statement once, however many statements hold it.
 *
 * <p>A condition read through a name used twice is held by two statements, so statements are a
 * graph, and the ways down a chain of names each using the one before it twice are two to its
 * length. A reader that recurses into the parts for itself pays for every way, and the readers that
 * did took longer than the whole of a compile at twenty-two names. Going down the parts is
 * {@link StatementReading}'s, and this is what keeps a reader that does not from being written
 * ({@link ReadersOfAGraph}), for a chain of each kind of statement that holds one.
 *
 * <p>That some readers were found is held ({@link #AT_LEAST_ASKED}) so that this cannot come to ask
 * none.
 */
@ClosedWorldContract
class EveryReaderOfAStatementAsksEachStatementOnceTest {

    /**
     * Readers whose work is the ways down, which is what they are for: a text of a statement is as
     * long as the ways down to its parts, and what a truth table is worked through for is every way
     * its distinct parts can come out.
     */
    private static final Map<String, String> BY_THEIR_NATURE = Map.of(
            "BorderQuantity$HowMany.said", "the text of the statement",
            "BorderQuantity$HowMany.grouped", "the text of the statement",
            "Proposition.spelledOut", "the text of the statement",
            "WhereEachLineDecides.held", "the message of the error it throws names the statement",
            "WhereEachLineDecides$Reading.of", "every way the distinct parts can come out",
            "TruthOutcomes.of", "every way the distinct parts can come out",
            "Proposition.toString", "the text of the statement");

    /** How many readers are asked at least, so that finding none is not a pass. */
    private static final int AT_LEAST_ASKED = 40;

    /**
     * Each statement holds the one before it twice: beside a statement of {@code kind} that holds
     * it, which is every kind that holds a statement in turn.
     */
    private static Proposition chainOf(Class<? extends Proposition> kind, int length) {
        String mine = UUID.randomUUID().toString();
        Proposition held = CompoundSamples.truth(mine + "0");
        for (int at = 1; at <= length; at++) {
            Proposition beside = CompoundSamples.truth(mine + at);
            // A conjunction and a disjunction are made as they are made anywhere, which joins one
            // inside another and so keeps no conjunction in a conjunction. A quantifier is not
            // read inside one over the same container.
            Proposition around = kind == Proposition.All.class ? Proposition.all(List.of(held,
                    beside)) : kind == Proposition.Any.class ? Proposition.any(List.of(held,
                    beside)) : CompoundSamples.holding(kind, held, beside,
                    new DecisionSubject.AnInput(TermPath.of("c" + at)));
            held = Proposition.all(List.of(held, around));
        }
        return held;
    }

    @Test
    void noReaderOfAStatementGoesDownEveryWayToItsParts() throws Exception {
        List<ReadersOfAGraph.Chain> chains = CompoundSamples.COMPOUNDS.stream()
                .map(kind -> new ReadersOfAGraph.Chain(kind.getSimpleName(), Proposition.class,
                        length -> chainOf(kind, length)))
                .toList();

        ReadersOfAGraph.Findings found = ReadersOfAGraph.askEach(chains, BY_THEIR_NATURE);

        assertEquals(Set.of(), found.slow(), "readers that take a growth of the ways down to "
                + "the parts on a chain of " + ReadersOfAGraph.LONG + " names as on one of "
                + ReadersOfAGraph.SHORT);
        assertTrue(found.asked() >= AT_LEAST_ASKED, found.asked() + " readers asked");
    }
}
