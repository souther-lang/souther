package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.WrittenOwner;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Where the arithmetic stops, it says why, and the reason is the one its rule met.
 *
 * <p>A reader that names a reason for a reading that stopped takes it from here
 * ({@link AffineForms.Halt}). Told from the kind of expression stopped at instead, a product of two
 * unknowns and a sum whose number has no representation are one operator and one answer, and a
 * quotient by nought reads as arithmetic no form says rather than as a number no run has.
 *
 * <p>Asked of the walk directly, over two names it calls atoms and one name that stands for two
 * values written out: each reason is met by the smallest expression that meets it.
 */
class AStopSaysWhyTheArithmeticStoppedThereTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final ConstructOccurrence WRITTEN = ConstructOccurrence.asWritten(
            SourceConstructOrigin.written(new WrittenOwner.Body("m", "f"), 0, SourceConstruct.IF));

    private static final Core X = name("x", 0, Type.INT);

    private static final Core Y = name("y", 1, Type.INT);

    /** A name for one of two values written out, which come to two different numbers. */
    private static final Core ONE_OF_TWO = name("either", 2, Type.INT);

    private static final Core XD = name("xd", 3, Type.DECIMAL);

    @Test
    void aProductOfTwoUnknownsIsNoLinearForm() {
        Core product = binary(BinOp.MUL, X, Y, Type.INT);
        AffineForms.Outcome.StoppedAt<String, String> stopped = stopOf(product);
        assertSame(product, stopped.node());
        assertInstanceOf(AffineForms.Halt.NotLinear.class, stopped.why());
        assertInstanceOf(AffineForms.Halt.NotLinear.class,
                stopOf(binary(BinOp.DIV, X, Y, Type.INT)).why(),
                "and a quotient by an unknown is the same");
    }

    @Test
    void aQuotientByNoughtHasNoNumberOnAnyRun() {
        Core quotient = binary(BinOp.DIV, X, new Core.Int(0, Type.INT, POS), Type.INT);
        AffineForms.Outcome.StoppedAt<String, String> stopped = stopOf(quotient);
        assertSame(quotient, stopped.node());
        assertInstanceOf(AffineForms.Halt.NoNumberOnARun.class, stopped.why());
        assertInstanceOf(AffineForms.Halt.NoNumberOnARun.class,
                stopOf(new Core.Neg(new Core.Int(Long.MIN_VALUE, Type.INT, POS), Type.INT, POS))
                        .why(),
                "and nor has the least whole number negated");
    }

    /**
     * A sum whose form is linear and whose number this arithmetic could not hold: the coefficient
     * of one term, a decimal far beyond what a whole number holds, beside one more of the same.
     */
    @Test
    void aSumWhoseNumberCannotBeHeldSaysSoAndNotThatItIsNoLinearForm() {
        Core far = new Core.Decimal(new BigDecimal(BigInteger.ONE, -2_000_000_000), Type.DECIMAL,
                POS);
        Core sum = binary(BinOp.ADD, binary(BinOp.MUL, XD, far, Type.DECIMAL), XD, Type.DECIMAL);
        AffineForms.Outcome.StoppedAt<String, String> stopped = stopOf(sum);
        assertSame(sum, stopped.node());
        assertInstanceOf(AffineForms.Halt.NotHeld.class, stopped.why());
    }

    @Test
    void valuesANameStandsForThatComeToTwoFormsSaySo() {
        AffineForms.Outcome.StoppedAt<String, String> stopped = stopOf(ONE_OF_TWO);
        assertSame(ONE_OF_TWO, stopped.node());
        assertInstanceOf(AffineForms.Halt.ValuesDisagree.class, stopped.why());
    }

    @Test
    void anExpressionWithNoRuleSaysThat() {
        Core text = new Core.Str("no number", Type.STRING, POS);
        assertInstanceOf(AffineForms.Halt.NoRule.class, stopOf(text).why());
    }

    /** And a part that stopped is the whole stop: the operator over it adds no reason of its own. */
    @Test
    void anOperatorOverAPartThatStoppedStopsWhereThePartDid() {
        Core product = binary(BinOp.MUL, X, Y, Type.INT);
        AffineForms.Outcome.StoppedAt<String, String> stopped =
                stopOf(binary(BinOp.ADD, product, X, Type.INT));
        assertSame(product, stopped.node());
        assertInstanceOf(AffineForms.Halt.NotLinear.class, stopped.why());
    }

    /** Which arithmetic no form says is the rule's to name, a product or a quotient. */
    @Test
    void theOperationIsTheOneTheRuleMet() {
        assertSame(NonAffineOperation.PRODUCT_OF_NON_CONSTANT_VALUES,
                stopOf(binary(BinOp.MUL, X, Y, Type.INT)).why().nonAffineOperation().orElseThrow());
        assertSame(NonAffineOperation.DIVISION_BY_NON_CONSTANT_VALUE,
                stopOf(binary(BinOp.DIV, X, Y, Type.INT)).why().nonAffineOperation().orElseThrow());
        assertEquals(Optional.empty(), stopOf(ONE_OF_TWO).why().nonAffineOperation());
    }

    /**
     * A stop under calls the library states the form of is the stop of what the call was handed, at
     * whatever depth, and it is the one place that says so.
     */
    @Test
    void theOperationIsFoundThroughTheCallsAnArgumentStoppedUnder() {
        AffineForms.Halt<String, String> product =
                new AffineForms.Halt.NotLinear<>(NonAffineOperation.PRODUCT_OF_NON_CONSTANT_VALUES);
        AffineForms.Halt<String, String> once = new AffineForms.Halt.AnArgumentStopped<>(
                new AffineForms.Outcome.StoppedAt<>(X, "at", product));
        AffineForms.Halt<String, String> twice = new AffineForms.Halt.AnArgumentStopped<>(
                new AffineForms.Outcome.StoppedAt<>(Y, "at", once));

        assertSame(NonAffineOperation.PRODUCT_OF_NON_CONSTANT_VALUES,
                twice.nonAffineOperation().orElseThrow());
        assertEquals(Optional.empty(),
                new AffineForms.Halt.AnArgumentStopped<String, String>(
                        new AffineForms.Outcome.StoppedAt<>(X, "at",
                                new AffineForms.Halt.NoRule<>())).nonAffineOperation(),
                "and a call whose argument stopped for something else says nothing of arithmetic");
    }

    private static Core name(String spelled, int index, Type type) {
        return new Core.Read(spelled, new BindingId(new BindingOwner.OfValue("m", "f"), index),
                type, POS);
    }

    private static Core binary(BinOp op, Core left, Core right, Type type) {
        return new Core.Binary(op, left, right, Core.BinaryReading.AS_THEY_STAND, WRITTEN, type,
                POS);
    }

    private static AffineForms.Outcome.StoppedAt<String, String> stopOf(Core e) {
        AffineForms.Outcome<String, String> read = AffineForms.outcome(e, "here", reading());
        if (read instanceof AffineForms.Outcome.StoppedAt<String, String> stopped) {
            return stopped;
        }
        throw new AssertionError("nothing composes a form of " + e + ", so the reading stopped: "
                + read);
    }

    /** Two names as atoms, and one name for two whole numbers written out. */
    private static AffineForms.Reading<String, String> reading() {
        return new AffineForms.Reading<>() {

            @Override
            public Symbols symbols() {
                return Symbols.none(DefaultStdlib.get());
            }

            @Override
            public DeclarationAccess declarations() {
                return DeclarationAccess.NONE;
            }

            @Override
            public LinearForm<String> leafOf(Core e, String at) {
                return Core.withoutStanding(e) instanceof Core.Read read
                        && !read.equals(ONE_OF_TWO) ? LinearForm.atom(read.name()) : null;
            }

            @Override
            public String inside(Core.LetIn li, String at) {
                return at;
            }

            @Override
            public AffineForms.ReadThrough<String> readThrough(Core.Read read, String at) {
                return null;
            }

            @Override
            public List<AffineForms.ReadThrough<String>> alternativesOf(Core.Read read,
                                                                        String at) {
                return read.equals(ONE_OF_TWO) ? List.of(
                        new AffineForms.ReadThrough<>(new Core.Int(1, Type.INT, POS), at),
                        new AffineForms.ReadThrough<>(new Core.Int(2, Type.INT, POS), at))
                        : null;
            }

            @Override
            public boolean readsThrough(Core.FieldAccess fa, String at) {
                return false;
            }
        };
    }
}
