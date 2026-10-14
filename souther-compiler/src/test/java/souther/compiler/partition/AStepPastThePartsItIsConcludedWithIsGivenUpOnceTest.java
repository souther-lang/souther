package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Conclusion;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.semantics.ConditionJoin;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A step whose statement, written out, comes to more parts than a step is concluded with is
 * concluded as a part nothing read, naming that figure — and that is what is kept of it, what a
 * reading asking again is handed, and what a rule reading the expression to the end is preferred
 * to.
 *
 * <p>Held on derivations made by hand, so the parts each comes to are counted here and not
 * guessed: a statement on each of {@code n} applications is {@code n} truths and the statement
 * holding them, and an {@code if} states its condition twice, where it holds and denied where it
 * does not, so one inside another doubles.
 */
class AStepPastThePartsItIsConcludedWithIsGivenUpOnceTest {

    private static final int MOST = CompositionBudget.PARTS_A_DERIVATION_CONCLUDES.maximum();

    private static final WhyUnread PAST_THE_PARTS = new WhyUnread.MorePartsThanAreConcluded();

    private static Derivation truth(String at) {
        return new Derivation.ATruthOfASubject(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    /** A statement on each of {@code applications} applications, each a truth of its own: that
     *  many parts and the one holding them. */
    private static Derivation onEach(int applications) {
        return onEach("x", applications);
    }

    private static Derivation onEach(String named, int applications) {
        List<Derivation> each = new ArrayList<>();
        for (int i = 0; i < applications; i++) {
            each.add(truth(named + i));
        }
        return new Derivation.OnEachApplication(each);
    }

    /** An {@code if} inside the condition of an {@code if}, {@code depth} deep: twice the parts at
     *  each step down, so past the figure however high it is set. */
    private static Derivation nested(int depth) {
        Derivation inside = truth("c");
        for (int i = 0; i < depth; i++) {
            inside = new Derivation.IfThenElse(inside, truth("yes" + i), truth("no" + i));
        }
        return inside;
    }

    private static int deepEnough() {
        return 2 + 32 - Integer.numberOfLeadingZeros(MOST);
    }

    @Test
    void asManyPartsAsTheFigureAreConcluded() {
        Proposition within = new Conclusion(Optional.empty()).of(onEach(MOST - 1));

        assertInstanceOf(Proposition.OnAnApplication.class, within);
        assertEquals(MOST - 1, ((Proposition.OnAnApplication) within).each().size());
    }

    @Test
    void onePartMoreIsAPartNothingReadNamingTheFigure() {
        Proposition past = new Conclusion(Optional.empty()).of(onEach(MOST));

        Proposition.Unread unread = assertInstanceOf(Proposition.Unread.class, past);
        assertEquals(PAST_THE_PARTS, unread.why());
        assertFalse(unread.fixed(), "a statement given up for its size is not known to be the same"
                + " whatever the input");
    }

    /** The steps inside are each within the figure; the one that doubles past it is given up, and
     *  so is every step holding it, which holds a part nothing read. */
    @Test
    void conditionsInsideOneAnotherStopAtTheStepThatPassesTheFigure() {
        Proposition past = new Conclusion(Optional.empty()).of(nested(deepEnough()));

        assertTrue(Proposition.stopsIn(past).contains(PAST_THE_PARTS),
                () -> "stopped at the figure: " + Proposition.stopsIn(past));
    }

    /**
     * A search from a node holds what it asks of a node and, where it is measured, that the node
     * has nothing below: both are parts, so both are counted. Each within the figure, the two
     * together past it.
     */
    @Test
    void whatASearchSaysOfNothingBelowIsCountedWithWhatItAsksOfANode() {
        int half = MOST / 2;
        Derivation atANode = onEach("node", half);
        Derivation searched = new Derivation.ATreeSearched(TermPath.of("t"), List.of("children"),
                atANode, Optional.of(List.of(onEach("below", half))), truth("unfolded"),
                ConditionJoin.EITHER);

        assertInstanceOf(Proposition.OnAnApplication.class,
                new Conclusion(Optional.empty()).of(atANode), "what it asks of a node is within");
        Proposition.Unread past = assertInstanceOf(Proposition.Unread.class,
                new Conclusion(Optional.empty()).of(searched));
        assertEquals(PAST_THE_PARTS, past.why());
    }

    /** A reading asking again is handed the step given up, and not the statement it gave up. */
    @Test
    void whatIsKeptOfAStepGivenUpIsThePartNothingRead() {
        Conclusion trying = Conclusion.reusing();
        Derivation step = onEach(MOST);

        Proposition first = trying.of(step);
        Proposition again = trying.of(step);

        assertInstanceOf(Proposition.Unread.class, first);
        assertSame(first, again);
        assertSame(first, trying.concludedAt(step));
    }

    /** A rule whose statement was given up for its size reads less of the expression than one
     *  that read all of it, and is kept only where nothing did better. */
    @Test
    void aRuleReadToTheEndIsPreferredToOneGivenUpForItsSize() {
        Derivation givenUp = onEach(MOST);
        Derivation whole = truth("whole");
        List<Supplier<Derivation>> both = List.of(() -> givenUp, () -> whole);
        List<Supplier<Derivation>> alone = List.of(() -> givenUp);

        assertSame(whole, RuleChoice.firstThatReadsIt(both, new ArrayList<>(),
                Conclusion.reusing()));
        assertSame(givenUp, RuleChoice.firstThatReadsIt(alone, new ArrayList<>(),
                Conclusion.reusing()));
    }
}
