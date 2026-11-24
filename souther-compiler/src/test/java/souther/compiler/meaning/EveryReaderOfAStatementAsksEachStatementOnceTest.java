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
 * <p>That the readers found going down every way answer, and are not merely asked and refused, is
 * held ({@link #MUST_ANSWER_ON_EVERY_CHAIN}), so that this cannot come to ask none.
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

    /**
     * Readers that answer on a chain of the kind named, so that being asked and refusing is not
     * what passes: the ones that were found going down every way, and the ones whose walk is the
     * model of what the rest do.
     */
    private static final Set<String> MUST_ANSWER_ON_EVERY_CHAIN = Set.of(
            "Proposition.whereItHolds on WhereItAnswers",
            "Proposition.whereItAnswersAtAll on WhereItAnswers",
            "Proposition.leavesSomethingUnread on All",
            "Proposition.saysASearchReachesBelow on SomeReachable",
            "Proposition.aboutAnAnswer on Some",
            "Proposition.mayTurnOnAnElementOf on Some",
            "Proposition.withTheValuesItHoldsCompared on Some",
            "TruthTable.holdsWhateverItsPartsAre on Any",
            "ReadThroughNames.atThePositions on Some",
            "Cutting.statesNoRelation on Any");

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
                        length -> chainOf(kind, length), Map.of(
                                DecisionSubject.class,
                                () -> new DecisionSubject.AnInput(TermPath.of("c1")),
                                TermPath.class, () -> TermPath.of("c1"),
                                Proposition.class, () -> CompoundSamples.truth("beside"),
                                String.class, () -> "f")))
                .toList();

        ReadersOfAGraph.Findings found = ReadersOfAGraph.askEach(chains, BY_THEIR_NATURE);

        assertEquals(Set.of(), found.slow(), "readers that take a growth of the ways down to "
                + "the parts on a chain of " + ReadersOfAGraph.LONG + " names as on one of "
                + ReadersOfAGraph.SHORT);
        Set<String> notAnswered = new java.util.TreeSet<>(MUST_ANSWER_ON_EVERY_CHAIN);
        notAnswered.removeAll(found.answered());
        assertEquals(Set.of(), notAnswered, "readers that were to answer and did not ("
                + found.answered().size() + " answered, " + found.refused().size() + " refused, "
                + found.notAsked().size() + " not asked)");
    }
}
