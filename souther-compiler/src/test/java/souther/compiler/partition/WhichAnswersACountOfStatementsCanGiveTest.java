package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;

import java.util.Comparator;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which answers a count of statements held as the count can give, read off which answers each
 * statement can give — without writing its choices out.
 *
 * <p>Said one way only where every count the statements could come to, each taken apart from the
 * others, says so. Two statements that cannot hold together are taken as though they could, so
 * what is said is every answer a run gives and maybe one it never does, and never one way where a
 * run could bring it out the other.
 */
class WhichAnswersACountOfStatementsCanGiveTest {

    private static final Proposition P =
            new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("p")), true);

    private static final Proposition Q =
            new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("q")), true);

    @Test
    void oneOfTwoThatEachMayHoldMayComeOutEitherWay() {
        assertEquals(TruthOutcomes.Outcomes.EITHER, TruthOutcomes.of(count(List.of(P, Q), 1)));
    }

    /** One statement that always holds beside one that may: one or two of them, never none. */
    @Test
    void everyCountTheStatementsComeToAdmittedIsTrueAlone() {
        assertEquals(TruthOutcomes.Outcomes.ONLY_TRUE,
                TruthOutcomes.of(count(List.of(new Proposition.Always(true), P), 1, 2)));
    }

    @Test
    void noCountTheStatementsComeToAdmittedIsFalseAlone() {
        assertEquals(TruthOutcomes.Outcomes.ONLY_FALSE,
                TruthOutcomes.of(count(List.of(new Proposition.Always(true), P), 0)));
    }

    /**
     * A statement and its denial never both hold, so two of them is never so; taken apart, they
     * could, and either way is said — an answer too many and not one too few.
     */
    @Test
    void statementsThatCannotHoldTogetherAreTakenAsThoughTheyCould() {
        assertEquals(TruthOutcomes.Outcomes.EITHER,
                TruthOutcomes.of(count(List.of(P, P.denied()), 2)));
    }

    /** How many of {@code statements} hold, each once, being one of {@code admitted}. */
    private static Proposition count(List<Proposition> statements, Integer... admitted) {
        List<Proposition> byKey = statements.stream()
                .sorted(Comparator.comparing(Proposition::spelledOut)).toList();
        return new Proposition.SoManyHold(byKey,
                Stream.generate(() -> 1).limit(byKey.size()).toList(), List.of(admitted));
    }
}
