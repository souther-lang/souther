package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.ReadersOfAGraph;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConditionJoin;
import souther.test.ClosedWorldContract;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.IntFunction;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every reader of a derivation asks each step once, however many steps hold it.
 *
 * <p>A value read through a name used twice is held by two steps, so derivations are a graph, and
 * the ways down a chain of names each using the one before it twice are two to its length
 * ({@link ReadersOfAGraph}). Asked of a chain of joins and a chain of ifs, each holding the step
 * before it in every place it can, and of chains whose lowest step is one the readers look for (a
 * comparison read, a run that stops) as well as of chains with none, since a reader that is asked
 * for what is not there is a different walk from one that is asked for what is.
 *
 * <p>Not asked of a chain of ifs that has a step to look for: each way down an {@code if} is a
 * different set of arms, and what is said is the relation for each of them, so what it is read in
 * is the ways. {@link ASharedDerivationIsReadAsTheUnsharedOneIsTest} holds what is said there.
 *
 * <p>That the readers found are asked and answer, and are not merely refused, is held
 * ({@link #MUST_ANSWER}), so that this cannot come to ask none.
 */
@ClosedWorldContract
class EveryReaderOfADerivationAsksEachStepOnceTest {

    /** Readers whose work is the ways down, which is what they are for. */
    private static final Map<String, String> BY_THEIR_NATURE = Map.of();

    /** Readers that answer on the chain of the kind named. */
    private static final Set<String> MUST_ANSWER = Set.of(
            "MeaningsOfABody$Meaning.relationsDownTheArmsOf on joins of comparisons read",
            "MeaningsOfABody$Meaning.relationsReadIn on joins of comparisons read",
            "MeaningsOfABody$Meaning.relationsDownTheArmsOf on joins of stops",
            "MeaningsOfABody$Meaning.relationsReadIn on joins of stops",
            "MeaningsOfABody$Meaning.relationsDownTheArmsOf on ifs with nothing to look for",
            "MeaningsOfABody$Meaning.relationsReadIn on ifs with nothing to look for");

    private static final Relation RELATION = new Relation.Affine(
            LinearForm.atom(new DecisionAtom.OfTheInput(
                    new NumericTerm.ValueOf(TermPath.of("x")))), Rel.GT);

    private static Derivation comparisonRead() {
        return new Derivation.AComparisonRead(Derivation.ComparisonReading.BY_A_LAW, RELATION,
                true, Derivation.AComparisonRead.Facing.NOTHING_WRITTEN);
    }

    private static Derivation joins(int length, Supplier<Derivation> lowest) {
        Derivation held = lowest.get();
        for (int at = 1; at <= length; at++) {
            held = new Derivation.Joined(at % 2 == 0 ? ConditionJoin.BOTH : ConditionJoin.EITHER,
                    held, held);
        }
        return held;
    }

    private static Derivation ifs(int length, Supplier<Derivation> lowest) {
        Derivation held = lowest.get();
        for (int at = 1; at <= length; at++) {
            held = new Derivation.IfThenElse(held, held, held);
        }
        return held;
    }

    private static ReadersOfAGraph.Chain chain(String label, IntFunction<Object> of,
                                               Map<Class<?>, Supplier<Object>> made) {
        return new ReadersOfAGraph.Chain(label, Derivation.class, of, made);
    }

    @Test
    void noReaderOfADerivationGoesDownEveryWayToItsSteps() throws Exception {
        Map<Class<?>, Supplier<Object>> made = Map.of(
                Conclusion.class, () -> new Conclusion(Optional.empty()),
                Derivation.class, () -> new Derivation.WrittenOut(true));
        Supplier<Derivation> nothing = () -> new Derivation.WrittenOut(true);
        ReadersOfAGraph.Findings found = ReadersOfAGraph.askEach(List.of(
                chain("joins of comparisons read",
                        length -> joins(length,
                                EveryReaderOfADerivationAsksEachStepOnceTest::comparisonRead),
                        made),
                chain("joins of stops", length -> joins(length, Derivation.TheRunStopsHere::new),
                        made),
                chain("joins with nothing to look for", length -> joins(length, nothing), made),
                chain("ifs with nothing to look for", length -> ifs(length, nothing), made)),
                BY_THEIR_NATURE);

        assertEquals(Set.of(), found.slow(), "readers that take a growth of the ways down to "
                + "the steps on a chain of " + ReadersOfAGraph.LONG + " names as on one of "
                + ReadersOfAGraph.SHORT);
        Set<String> notAnswered = new TreeSet<>(MUST_ANSWER);
        notAnswered.removeAll(found.answered());
        assertEquals(Set.of(), notAnswered, "readers that were to answer and did not ("
                + found.answered().size() + " answered, " + found.refused().size() + " refused, "
                + found.notAsked().size() + " not asked)");
    }
}
