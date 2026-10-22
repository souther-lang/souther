package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.Count;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * How often a value occurs among the occurrences a statement keeps is read back from the values
 * the walk found only where the statement was told of every one of them: an occurrence it could not
 * be put to may be the value counted and kept, so the count made without it is a floor and no
 * count.
 */
class ACountAmongKeptOccurrencesIsReadBackOnlyWhereTheStatementToldEveryOneTest {

    private static final TermPath LINES = TermPath.of("orders").element().then("lines");
    private static final TermPath SKU = LINES.element();

    private static final Proposition HAS_A_VALUE =
            new Proposition.Present(new DecisionSubject.AnInput(SKU), true);

    private static final ObservedValue CUT_SHORT =
            new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure());

    private static TermOrders keptWhereThereIsAValue() {
        KeptOccurrences kept = new KeptOccurrences(new DecisionSubject.AnInput(LINES),
                HAS_A_VALUE, AStatementAtARow.of(HAS_A_VALUE, "f", null));
        return TermOrdersFixtures.itself(NumericTerm.OccurrencesOfItsValue.of(
                new RunSource.FlattenedOccurrences(SKU), kept), Carrier.TEXT);
    }

    @Test
    void aCountOfTheOccurrencesTheStatementKeptStandsWhereItToldEveryOne() {
        assertInstanceOf(Generator.RealizationReadback.AtRequestedPlace.class,
                Generator.readBack(keptWhereThereIsAValue(), List.of(
                        new ObservedValue.Text("x"), new ObservedValue.Text("x"),
                        new ObservedValue.Absent()), Count.of(2)),
                "x is kept twice, and the dropped one is known to be dropped");
    }

    @Test
    void aCountIsNoneWhereTheStatementCouldNotBePutToAnOccurrence() {
        assertInstanceOf(Generator.ReadbackGap.KeptNotTold.class,
                assertInstanceOf(Generator.RealizationReadback.CouldNotTell.class,
                        Generator.readBack(keptWhereThereIsAValue(), List.of(
                                new ObservedValue.Text("x"), new ObservedValue.Text("x"),
                                CUT_SHORT), Count.of(2))).why(),
                "the one cut short may be a third x that is kept");
    }
}
