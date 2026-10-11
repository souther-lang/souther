package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Whether a row put one value at two positions is told only of values every part of which was read.
 *
 * <p>A record a limit stopped in one of its fields is a value all the same, and two of them stopped
 * alike are equal as values while what was written in them may differ. Held against each other as
 * they are, a key an entry was filed under would be said to be the key asked for where nothing shows
 * it.
 */
class TwoValuesAreOneOnlyWhereAllOfBothWasReadTest {

    private static final TermPath ONE = TermPath.of("one");

    private static final TermPath OTHER = TermPath.of("other");

    private static AStatementAtARow.Answer theSameAt(ObservedValue one, ObservedValue other) {
        AStatementAtARow statement = AStatementAtARow.of(new Proposition.SameValue(
                new DecisionSubject.AnInput(ONE), new DecisionSubject.AnInput(OTHER), true),
                "decide", null);
        return statement.at(new BorderQuantity.Observation() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                return WalkResult.reached(new ObservationAtPoint.Value(
                        path.equals(ONE) ? one : other));
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a sameness reads one value at each position");
            }

            @Override
            public WalkResult<List<BorderQuantity.Observation>> eachElementOf(
                    TermPath container) {
                throw new AssertionError("a sameness of two positions walks no container");
            }
        });
    }

    private static ObservedValue key(ObservedValue code) {
        return new ObservedValue.Constructed(TypeSymbols.declared(new TypeKey("g", "Key")),
                Map.of("code", code));
    }

    private static AStatementAtARow.Answer couldNotTell(Incompleteness.Code why) {
        return new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.of(why)));
    }

    @Test
    void twoRecordsStoppedAlikeAreNotSaidToBeOne() {
        assertEquals(couldNotTell(Incompleteness.Code.VALUE_TRUNCATED),
                theSameAt(key(new ObservedValue.Truncated()), key(new ObservedValue.Truncated())));
        assertEquals(couldNotTell(Incompleteness.Code.VALUE_UNREADABLE),
                theSameAt(key(new ObservedValue.Text("A")), key(new ObservedValue.Unknown("no"))));
    }

    @Test
    void aValueThatWasNotReadIsNotSaidToBeOneOrTwo() {
        assertEquals(couldNotTell(Incompleteness.Code.VALUE_TRUNCATED),
                theSameAt(new ObservedValue.Truncated(), new ObservedValue.Text("A")));
    }

    /** The control: records read whole are one where they hold the same and two where not. */
    @Test
    void recordsReadWholeAreOneOrTwoAsTheyHold() {
        assertEquals(AStatementAtARow.Answer.HOLDS,
                theSameAt(key(new ObservedValue.Text("A")), key(new ObservedValue.Text("A"))));
        assertEquals(AStatementAtARow.Answer.FAILS,
                theSameAt(key(new ObservedValue.Text("A")), key(new ObservedValue.Text("B"))));
    }
}
