package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The row is read to find out which readings of it there are, and where that reading is one of
 * them it is not made again.
 *
 * <p>Which readings a row has is the quantity's to say as it reads the row, so the readings are
 * found by reading it once and taking every choice the steps that reading recorded allow. Where the
 * row's positions take no steps there is one choice and it is the empty one — the choice the row was
 * just read under — so the reading made to find the readings is the reading of the only one there
 * is.
 *
 * <p><b>And where there are steps it is not one of them.</b> Every choice then names an element, and
 * a reading that names one is not the reading that names none: the first takes that element and the
 * second takes the first value that agrees. So the pair below is what says which of the two a row
 * is, rather than a rule that a reading is always there to be had.
 */
class TheReadingTheStepsWereFoundByIsOneOfTheReadingsTriedTest {

    private static final String MODEL = """
            module g

            data Line = { amount: Int }

            data Page = { count: Int }

            behavior decide : (flat: Int, lines: List<Line>) -> Page
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            souther.compiler.values.AsACompilationAllows.admittedValues(),
            souther.compiler.values.AsACompilationAllows.whatARuleLeaves());

    private static final TermPath FLAT = TermPath.of("flat");

    private static final TermPath AN_AMOUNT = TermPath.of("lines").element().then("amount");

    @Test
    void aRowWhosePositionsTakeNoStepsHasTheReadingItWasReadUnder() {
        StandingAtAPoint.Readings readings = readingsOf(FLAT,
                List.of(new ObservedValue.Integer(7), new ObservedValue.Sequence(List.of())));

        assertEquals(1, readings.tried().size(),
                "a position outside a sequence gives one reading of the row");
        assertEquals(List.of(quantityOf(FLAT).read(readings.tried().get(0))), readings.made(),
                "and what was kept is the reading of it, so it is not read again");
    }

    @Test
    void aRowWhosePositionsTakeStepsHasNoneOfThemRead() {
        StandingAtAPoint.Readings readings = readingsOf(AN_AMOUNT,
                List.of(new ObservedValue.Integer(7),
                        new ObservedValue.Sequence(List.of(line(3), line(4)))));

        assertEquals(2, readings.tried().size(),
                "one reading per element the position holds");
        assertEquals(List.of(), readings.made(),
                "each of them names an element, and none of them is the reading that names none");
    }

    private static StandingAtAPoint.Readings readingsOf(TermPath at, List<ObservedValue> row) {
        RuleReadingSource rules = RuleReadings.ofSource(MODEL);
        BehaviorInputs where = new BehaviorInputs(List.of("flat", "lines"),
                List.of(Type.Prim.INT, new Type.ListOf(named("Line"))), rules, POLICY);
        return StandingAtAPoint.readings(where,
                new ObservedInputs(row, new Generator.Watched.NoAccount()), quantityOf(at),
                new LinkedHashMap<>());
    }

    private static BorderQuantity quantityOf(TermPath at) {
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(at);
        return new BorderQuantity.OfACoordinate("decide", term,
                TermOrdersFixtures.itself(term, new Carrier.Whole()));
    }

    private static ObservedValue line(int amount) {
        return new ObservedValue.Constructed(sym("Line"),
                Map.of("amount", new ObservedValue.Integer(amount)));
    }

    private static Type named(String data) {
        return Type.ref(sym(data));
    }

    private static TypeSymbol sym(String data) {
        return TypeSymbols.declared(new TypeKey("g", data));
    }
}
