package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountingUnit;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.math.BigDecimal;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A form over positions written back differently is read, and one whose counts mean different
 * things is not.
 *
 * <p>What a form needs of its positions is that their counts mean one thing, and that is not the
 * same as their being written back the same way. A {@code Decimal} and an {@code Int} are two orders
 * and one of each is one, so their difference is a number; a date counts days, so a date and a
 * number have no sum however well both sides type-checked.
 *
 * <p>One rule stood in for both. A quantity answered with the one order every position under it was
 * on — which a coordinate and a line between two positions have — and a form was held to the same,
 * so every form whose positions merely wrote back differently was refused along with the ones that
 * could not be added at all. Nothing said so: the reading returned no quantity, and a rule the model
 * states drew no border.
 */
class AFormAddsPositionsWrittenBackDifferentlyTest {

    private static final String A_DECIMAL_AN_INT_AND_A_DATE = """
            module example.mixed

            data Amount = Decimal
                invariant value >= 0
                invariant value <= 10

            data Steps = Int
                invariant value >= 0
                invariant value <= 10

            data P = { d: Amount, n: Steps, on: Date }

            data Yes = { v: Int }

            behavior take : (p: P) -> Yes
                constructs Yes
            let take (p) = Yes { v = 1 }
            """;

    private static NumericTerm value(String field) {
        return new NumericTerm.ValueOf(TermPath.of("p").then(field));
    }

    /** {@code d - n}, the difference of a decimal position and a whole-number one. */
    private static NumericDomain.LinearForm<NumericTerm> aDecimalLessAnInt() {
        return new NumericDomain.LinearForm<>(BigDecimal.ZERO,
                Map.of(value("d"), BigDecimal.ONE, value("n"), BigDecimal.ONE.negate()));
    }

    /** What a decimal and a whole number are counted in, which is the same thing. */
    @Test
    void aDecimalAndAWholeNumberCountTheSameThing() {
        assertEquals(Carrier.WHOLE.counting(), Carrier.DENSE.counting(),
                "one of each is one, which is what a form adds");
        assertTrue(!Carrier.DATE.counting().equals(Carrier.WHOLE.counting()),
                "and a day is not a number, so a date and an Int have no sum");
        assertTrue(!Carrier.TEXT.counting().counts(),
                "a string counts nothing, so nothing adds it to anything");
    }

    /** The form the whole of this is about: two positions, two orders, one unit. */
    @Test
    void aFormOverTwoOrdersThatCountTheSameThingIsAQuantity() {
        BorderQuantity.OverAForm over = new BorderQuantity.OverAForm("take",
                aDecimalLessAnInt(),
                Map.of(value("d"), Carrier.DENSE, value("n"), Carrier.WHOLE));

        assertEquals(Carrier.DENSE, over.carrierOf(value("d")),
                "the decimal position is read and written as a decimal");
        assertEquals(Carrier.WHOLE, over.carrierOf(value("n")),
                "and the whole-number position as a whole number");
        assertEquals(null, over.carrierOf(value("on")),
                "and a position the form is not over has no order under this quantity");
    }

    /**
     * And its levels are dense, which is the sum's answer and not any one position's.
     *
     * <p>A whole number added to a decimal lands wherever the decimal does. Read off a single order
     * handed to the form, this was whatever that order said — so a form the search had to step
     * through would have been stepped through by ones.
     */
    @Test
    void whatTheSumStepsByIsWhatItsPositionsStepByTogether() {
        BorderQuantity.OverAForm mixed = new BorderQuantity.OverAForm("take",
                aDecimalLessAnInt(),
                Map.of(value("d"), Carrier.DENSE, value("n"), Carrier.WHOLE));
        BorderQuantity.OverAForm whole = new BorderQuantity.OverAForm("take",
                aDecimalLessAnInt(),
                Map.of(value("d"), Carrier.WHOLE, value("n"), Carrier.WHOLE));

        assertEquals(souther.compiler.numeric.Granularity.DENSE, mixed.spacing(),
                "one dense position makes the sum dense");
        assertEquals(souther.compiler.numeric.Granularity.DISCRETE, whole.spacing(),
                "and a form of whole numbers answers what it always did");
    }

    /** A form adding counts that do not mean the same thing is refused where it is built. */
    @Test
    void aFormOverPositionsWhoseCountsMeanDifferentThingsIsRefused() {
        NumericDomain.LinearForm<NumericTerm> aDateLessAnInt =
                new NumericDomain.LinearForm<>(BigDecimal.ZERO,
                        Map.of(value("on"), BigDecimal.ONE, value("n"), BigDecimal.ONE.negate()));

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new BorderQuantity.OverAForm("take", aDateLessAnInt,
                        Map.of(value("on"), Carrier.DATE, value("n"), Carrier.WHOLE)));
        assertTrue(refused.getMessage().contains("do not count the same thing"),
                refused.getMessage());
    }

    /**
     * An order for a position the form does not name, and a position with no order, are both
     * refused.
     *
     * <p>Two structures are what come apart. The orders are written beside the form and could name
     * a position it does not have, or leave one of its own with nothing to be read on — and a reader
     * meeting the second has a position and no way to read it, which is the answer it would have had
     * to invent.
     */
    @Test
    void aFormAndItsOrdersAreOverTheSamePositions() {
        assertTrue(assertThrows(IllegalArgumentException.class,
                () -> new BorderQuantity.OverAForm("take", aDecimalLessAnInt(),
                        Map.of(value("d"), Carrier.DENSE)))
                .getMessage().contains("read on one order"));
        assertTrue(assertThrows(IllegalArgumentException.class,
                () -> new BorderQuantity.OverAForm("take", aDecimalLessAnInt(),
                        Map.of(value("d"), Carrier.DENSE, value("n"), Carrier.WHOLE,
                                value("on"), Carrier.DATE)))
                .getMessage().contains("read on one order"));
    }

    /**
     * And the whole way through: a level of such a form comes back as a row.
     *
     * <p>Through {@link BorderQuantity#standingAt} and {@link LevelRealizer} rather than asserted of
     * the quantity, because what the single order was reaching was the search — which walked every
     * position over the values of whichever order it had been handed. A decimal position walked by
     * whole numbers finds a row at some levels and not at others, and which is which is nothing a
     * reader could have named.
     */
    @Test
    void aLevelOfSuchAFormIsReached() {
        BorderQuantity.OverAForm over = new BorderQuantity.OverAForm("take",
                aDecimalLessAnInt(),
                Map.of(value("d"), Carrier.DENSE, value("n"), Carrier.WHOLE));

        Standing standing = over.standingAt(
                new Criterion.AtTheLevel(new Level.ACount(Count.of(new BigDecimal("2.5")))));

        assertInstanceOf(Standing.OfAForm.class, standing);
        assertEquals(Map.of(value("d"), Carrier.DENSE, value("n"), Carrier.WHOLE),
                ((Standing.OfAForm) standing).on(),
                "the standing carries an order per position, which is what the search reads");
        assertInstanceOf(Realization.Found.class,
                new LevelRealizer().realize(standing, region()),
                "a difference of two and a half is reached by a decimal and a whole number, and by"
                        + " no two whole numbers");
    }

    /** What one is, on each of the orders. Read here so a carrier added answers it. */
    @Test
    void everyOrderSaysWhatOneOfItsCountsIs() {
        assertEquals(CountingUnit.A_NUMBER, Carrier.WHOLE.counting());
        assertEquals(CountingUnit.A_NUMBER, Carrier.DENSE.counting());
        assertEquals(CountingUnit.DAYS, Carrier.DATE.counting());
        assertEquals(CountingUnit.SECONDS, Carrier.MOMENT.counting());
        assertEquals(CountingUnit.SECONDS_OF_A_DAY, Carrier.TIME.counting());
        assertEquals(CountingUnit.NANOSECONDS, Carrier.INSTANT.counting());
        assertEquals(CountingUnit.NOT_COUNTED, Carrier.TEXT.counting());
    }

    private static SearchRegion region() {
        Compilation compilation = Compilation.ofSource(A_DECIMAL_AN_INT_AND_A_DATE, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("take")).findFirst().orElseThrow();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        return InputDomain.of(spec, sigs.get("take"), symbols, ReadAs.THE_COMPILATION_DOES)
                .quantities(symbols).region();
    }
}
