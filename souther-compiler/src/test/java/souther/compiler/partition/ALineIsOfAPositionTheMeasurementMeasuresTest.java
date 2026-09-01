package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.Carrier;
import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.RuleRef;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A line a measurement reads is a line on a position that measurement measures.
 *
 * <p>Two questions and not one. That the reading answers for the number the line cuts is what says
 * the line was drawn at this input rather than at another behavior's spelled the same way; that the
 * measurement has a measure there is what says the model divides or bounds the place at all. A
 * reading answers for every position it read, and the model measures only some of them — so a term
 * the reading knows is not by itself a place a line can be read at.
 *
 * <p>Held apart because they break apart. A line brought in from another reading fails the first;
 * a line on a position this behavior has and nothing measures fails the second, and its number is
 * one this reading answers for perfectly well.
 */
class ALineIsOfAPositionTheMeasurementMeasuresTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    private static final Carrier WHOLE = new Carrier.Whole();

    /** The reading of an input of one parameter apiece, all of them plain numbers. */
    private static InputReading readingOf(String... parameters) {
        List<InputDomain.Parameter> declared = new ArrayList<>();
        for (String each : parameters) {
            declared.add(new InputDomain.Parameter(each, null, Type.INT));
        }
        return InputDomain.of(declared, SYMBOLS, ReadAs.THE_COMPILATION_DOES).reading(SYMBOLS);
    }

    private static NumericTerm.ValueOf number(String parameter) {
        return new NumericTerm.ValueOf(TermPath.of(parameter));
    }

    /** A measure that bounds the number at that parameter and divides it into nothing, which is
     *  what a rule that only caps a value leaves. */
    private static Axis bounding(String behavior, String parameter) {
        NumericTerm.ValueOf number = number(parameter);
        return new Axis(AxisId.of(behavior, number), number, List.of(),
                List.of(new Cut(WHOLE, Count.of(100), List.of(aBound()))));
    }

    /** A line at a hundred on the number that parameter holds. */
    private static Border lineOn(String behavior, String parameter) {
        NumericTerm.ValueOf number = number(parameter);
        return Border.at(BoundaryTarget.at(
                        new BorderQuantity.OfACoordinate(behavior, number,
                                TermOrdersFixtures.itself(number, WHOLE)),
                        new Level.OnACarrier(WHOLE, Count.of(100))),
                aBound(),
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(100)),
                        Endpoint.inclusive(Count.of(1000))));
    }

    private static OriginRef aBound() {
        return new OriginRef.InvariantOrigin(new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("example.fee", "Amount")), 0),
                Optional.of(new ClauseName("cap")))), 0, EndSide.LOWER, true);
    }

    /** The line the measurement's own measure was cut on is read. */
    @Test
    void aLineWhereTheMeasurementMeasuresIsRead() {
        MeasuredInput subject = MeasuredInput.of("fee", readingOf("days"),
                AxesATestWrote.asAMeasurement("fee", List.of(bounding("fee", "days"))));

        assertNotNull(subject.at(lineOn("fee", "days")),
                "the reading answers for the number and the model measures the position");
    }

    /**
     * And a line on a position the reading knows and nothing measures is not.
     *
     * <p>The number is one this input has and one this reading answers for, so the term half of the
     * question passes. What it has no measure at is the position, and a reading of the line there
     * would be a reading of a place this measurement never went.
     */
    @Test
    void aLineWhereNothingMeasuresIsRefused() {
        MeasuredInput subject = MeasuredInput.of("fee", readingOf("days", "cap"),
                AxesATestWrote.asAMeasurement("fee", List.of(bounding("fee", "days"))));

        assertNotNull(subject.quantities().ordersOf(number("cap")),
                "the reading answers for the number the refused line is on");

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> subject.at(lineOn("fee", "cap")));
        assertEquals("a line at fee/cap, which is no position this measurement measures: fee",
                refused.getMessage());
    }

    /**
     * The name a coordinate is under is the number it cuts, so the two cannot disagree.
     *
     * <p>Which is why the question above is worth asking at all. Given the name beside the number,
     * a line could be filed under one position while cutting another, and asking whether the
     * measurement measures the name would answer about a place the line is not on.
     */
    @Test
    void aCoordinateIsNamedAfterTheNumberItCuts() {
        NumericTerm.ValueOf number = number("days");
        BorderQuantity.OfACoordinate cut = new BorderQuantity.OfACoordinate("fee", number,
                TermOrdersFixtures.itself(number, WHOLE));

        assertEquals(AxisId.of("fee", number), cut.axis());
        assertEquals(cut.axis(), cut.onAPosition(),
                "which is the position a reader asks the quantity for");
    }
}
