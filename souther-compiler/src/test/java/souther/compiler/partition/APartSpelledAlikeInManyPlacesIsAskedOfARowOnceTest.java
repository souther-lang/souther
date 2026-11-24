package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A part a statement says in two places, made as two objects, is asked of a row once, and each
 * row is asked afresh.
 */
class APartSpelledAlikeInManyPlacesIsAskedOfARowOnceTest {

    private static final TermPath A = TermPath.of("a");

    private static final TermPath B = TermPath.of("b");

    private static Proposition present(TermPath at) {
        return new Proposition.Present(new DecisionSubject.AnInput(at), true);
    }

    /** What the row put at each position, and each position the statement asked about. */
    private static AStatementAtARow.Answer at(AStatementAtARow statement,
                                              Map<TermPath, ObservedValue> row,
                                              List<TermPath> asked) {
        return statement.at(new BorderQuantity.Observation() {

            @Override
            public Place fixedAt(NumericTerm term) {
                return null;
            }

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                asked.add(path);
                return WalkResult.reached(new ObservationAtPoint.Value(row.get(path)));
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a presence reads one value");
            }

            @Override
            public WalkResult<List<BorderQuantity.Observation>> eachElementOf(
                    TermPath container) {
                throw new AssertionError("a presence walks no container");
            }
        });
    }

    @Test
    void eachRowIsAskedOnceForEachPartWhateverNumberOfPlacesSayIt() {
        AStatementAtARow statement = AStatementAtARow.of(new Proposition.All(List.of(
                present(A), new Proposition.Any(List.of(present(A), present(B))))),
                "decide", null);
        ObservedValue there = new ObservedValue.Text("x");
        ObservedValue nothing = new ObservedValue.Absent();

        List<TermPath> first = new ArrayList<>();
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(statement, Map.of(A, there, B, nothing), first));
        assertEquals(List.of(A, B), first);

        List<TermPath> second = new ArrayList<>();
        assertEquals(AStatementAtARow.Answer.FAILS,
                at(statement, Map.of(A, nothing, B, there), second));
        assertEquals(List.of(A, B), second);
    }
}
