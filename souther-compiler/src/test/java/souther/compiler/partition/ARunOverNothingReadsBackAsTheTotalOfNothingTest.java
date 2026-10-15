package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.Carrier;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A total over a run that stands in no value is the total of nothing, and a row that wrote none
 * reads back as it.
 *
 * <p>{@code entries = []} holds no posting, so no posting stands at the path a run is read from —
 * and the run is there all the same, and what it adds up to is nought. A reading back that turned
 * away an empty walk before asking which kind of number it was reading answered "nothing stands
 * there" for a number that has an answer, and a total of nought was a point no candidate was ever
 * read back at. The number one position answers is the other way round: it has no number of no
 * value.
 */
class ARunOverNothingReadsBackAsTheTotalOfNothingTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    private static final TermPath POSTINGS = TermPath.of("ledger").then("entries").element()
            .then("postings");

    private static NumericTerm.TakenOver total(RunSource run) {
        NumericTerm.TakenOver total = NumericTerm.TakenOver.of(
                ValueName.Stdlib.operation("List", "sum"), run, Type.INT,
                ScopedDeclarations.wrapsOf(SYMBOLS), SYMBOLS);
        assertNotNull(total, "adding up whole numbers is a number of a run");
        return total;
    }

    private static Generator.RealizationReadback readBack(NumericTerm term,
                                                          List<ObservedValue> values, long at) {
        TermOrders orders = TermOrdersFixtures.at(term, Type.INT, SYMBOLS);
        return Generator.readBack(orders, values, Count.of(at));
    }

    /** Over one container and over several, each of them. */
    @Test
    void aRunOverNoValuesReadsBackAsNought() {
        for (RunSource run : List.of(
                new RunSource.ProjectedOccurrences(TermPath.of("ledger").then("entries")
                        .element().then("q")),
                new RunSource.FlattenedOccurrences(POSTINGS.element().then("q")))) {
            NumericTerm.TakenOver total = total(run);
            assertInstanceOf(Generator.RealizationReadback.AtRequestedPlace.class,
                    readBack(total, List.of(), 0),
                    run + ": a run of nothing is a total of nought");
            assertInstanceOf(Generator.RealizationReadback.Elsewhere.class,
                    readBack(total, List.of(), 3),
                    run + ": and a candidate built for another total is not at it");
        }
    }

    /** What a run that has values comes to is what they add up to, as it was. */
    @Test
    void aRunOverValuesReadsBackAsTheirTotal() {
        NumericTerm.TakenOver total = total(new RunSource.FlattenedOccurrences(
                POSTINGS.element().then("q")));
        List<ObservedValue> values = List.of(new ObservedValue.Integer(2),
                new ObservedValue.Integer(1), new ObservedValue.Integer(1));
        assertInstanceOf(Generator.RealizationReadback.AtRequestedPlace.class,
                readBack(total, values, 4));
        assertInstanceOf(Generator.RealizationReadback.Elsewhere.class,
                readBack(total, values, 3));
    }

    /** A number one position answers has no number of no value, and says so. */
    @Test
    void aNumberOfOnePositionHasNoNumberOfNoValue() {
        NumericTerm.FromOnePosition one = new NumericTerm.ValueOf(POSTINGS.element().then("q"));
        TermOrders orders = TermOrdersFixtures.itself(one, Carrier.WHOLE);
        Generator.RealizationReadback read =
                Generator.readBack(orders, List.of(), Count.of(0));
        assertEquals(Generator.ReadbackGap.NoValueAtThePosition.class, assertInstanceOf(
                Generator.RealizationReadback.CouldNotTell.class, read).why().getClass());
    }
}
