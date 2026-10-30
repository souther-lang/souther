package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.CountsWrittenOut;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Spelling;

import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a count of statements held as the count turns on is what its choices written out turn on:
 * every statement it counts, either way round, and nothing of the count's own spelling.
 *
 * <p>Held against the choices themselves, since those are what a reader of the count would be
 * handed, and a part turned on is a part some reader asks a row about.
 */
class ACountOfStatementsTurnsOnWhatItsChoicesTurnOnTest {

    @Test
    void aCountTurnsOnEachStatementItCounts() {
        List<Proposition> statements = IntStream.range(0, 4)
                .mapToObj(at -> (Proposition) new Proposition.Truth(
                        new DecisionSubject.AnInput(TermPath.of("t" + at)), true))
                .sorted(Comparator.comparing(Proposition::spelledOut)).toList();
        Proposition.SoManyHold counted = new Proposition.SoManyHold(statements,
                List.of(1, 1, 1, 1), List.of(2));
        Proposition choices = CountsWrittenOut.of(counted)
                instanceof CountsWrittenOut.Written(Proposition written) ? written : null;
        assertNotNull(choices, "six choices of four statements are written out for a reader");

        Set<Spelling> ofTheCount = new HashSet<>();
        Pullback.Pulled.partsOf(counted, ofTheCount);
        Set<Spelling> ofTheChoices = new HashSet<>();
        Pullback.Pulled.partsOf(choices, ofTheChoices);

        assertEquals(ofTheChoices, ofTheCount);
        assertFalse(ofTheCount.contains(counted.spelling()), "the count itself is no part of it");
    }
}
