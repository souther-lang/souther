package souther.program.api;

import souther.compiler.abort.AbortKind;
import souther.compiler.core.Contract;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@link CheckedProgram#abortsAt} answers for a {@code Core} site, read against the same
 * fixtures a source author would write — never against a node built by hand, which would be asking
 * this compiler's own opinion of a shape it invented rather than of a program it checked.
 */
class ACoreSiteAnswersWhichLanguageAbortsItCanRaiseTest {

    private static final String MODULE = """
            module demo exposing
                ( Positive, unguarded, guarded, sums
                , dividesIntByInt, dividesDecimalByDecimal, dividesWithARationalOperand
                , unreached
                , negatesInt, negatesDecimal, negatesRational
                , Span, LabeledSpan, bounded
                )

            data Positive = Int
                invariant positive = value > 0

            data Span = { lo: Int, hi: Int }
                invariant ordered = lo + 1 <= hi

            data LabeledSpan = { ...Span, label: String }

            behavior bounded : (n: Int) -> Int
                ensures above = value + 1 > n

            let bounded (n) = n

            behavior unguarded : (n: Int) -> Positive

            let unguarded (n) = Positive(n)

            behavior guarded : (n: Int) -> Positive

            let guarded (n) = {
                guard Positive(n) as p else Positive(1)

                p
            }

            behavior sums : (a: Int, b: Int) -> Int

            let sums (a, b) = a + b

            behavior dividesIntByInt : (a: Int, b: Int) -> Int

            let dividesIntByInt (a, b) = Rational.toInt(DOWN, a / b)

            behavior dividesDecimalByDecimal : (a: Decimal, b: Decimal) -> Int

            let dividesDecimalByDecimal (a, b) = Rational.toInt(DOWN, a / b)

            behavior dividesWithARationalOperand : (a: Int, b: Int, c: Int) -> Int

            let dividesWithARationalOperand (a, b, c) = Rational.toInt(DOWN, (a / b) / c)

            behavior unreached : (n: Int) -> Int

            let unreached (n) = unreachable "never called with anything"

            behavior negatesInt : (n: Int) -> Int

            let negatesInt (n) = -n

            behavior negatesDecimal : (n: Decimal) -> Decimal

            let negatesDecimal (n) = -n

            behavior negatesRational : (a: Int, b: Int) -> Int

            let negatesRational (a, b) = Rational.toInt(DOWN, -(a / b))
            """;

    private static CheckedProgram program() {
        return CheckedProgram.of(List.of(MODULE));
    }

    private static Core bodyOf(CheckedProgram program, String behavior) {
        CheckedModule demo = program.module("demo");
        for (var b : demo.behaviors()) {
            if (b.name().name().equals(behavior)) {
                return ((CheckedImplementation.Body) b.implementation()).body();
            }
        }
        throw new AssertionError("no behavior `" + behavior + "` in the fixture");
    }

    /** Every node under {@code root}, {@code root} itself included — a plain walk, independent of
     *  {@code AbortSites}, so this test reads the body rather than the classifier's own opinion of
     *  it. */
    private static List<Core> everyNodeOf(Core root) {
        List<Core> found = new ArrayList<>();
        collect(root, found);
        return found;
    }

    private static void collect(Core node, List<Core> into) {
        into.add(node);
        Core.forEachChild(node, child -> collect(child, into));
    }

    @Test
    void aPlainConstructionAbortsOnAnUnheldInvariant() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "unguarded");

        Core.Construct construct = onlyOneOf(Core.Construct.class, body);

        assertEquals(Set.of(AbortKind.INVARIANT_NOT_HELD), program.abortsAt(construct).kinds());
    }

    /**
     * And the same construction, attempted, never does — the invariant decides a branch instead of
     * aborting, so the site {@code guard ... as ... else ...} tests has nothing to answer for.
     */
    @Test
    void anAttemptedConstructionNeverAbortsOnTheInvariantItTests() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "guarded");

        Core.IfConstructed attempt = onlyOneOf(Core.IfConstructed.class, body);

        assertTrue(program.abortsAt(attempt).isEmpty(),
                "the IfConstructed itself branches; it does not abort");
        assertTrue(program.abortsAt(attempt.construct()).isEmpty(),
                "the construction it tests is guarded, so its own invariant is not an abort here");
    }

    @Test
    void anIntSumAbortsWhereTheAnswerHasNoPlace() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "sums");

        Core.Binary sum = onlyOneOf(Core.Binary.class, body);

        assertEquals(Set.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE), program.abortsAt(sum).kinds());
    }

    /**
     * Unary minus on {@code Int} aborts the same way {@code +}/{@code -}/{@code *} do (spec
     * §stdlib-int, issue #1878): the smallest {@code Int} has no positive counterpart. Fixed at this
     * layer and not only at {@code BodyGen}'s — a classifier answering {@link AbortSet#NONE} again
     * here would leave the JVM execution test green, since {@code BodyGen}'s emission does not read
     * {@code AbortSites} back.
     */
    @Test
    void intNegationAbortsWhereTheAnswerHasNoPlace() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "negatesInt");

        Core.Neg neg = onlyOneOf(Core.Neg.class, body);

        assertEquals(Set.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE), program.abortsAt(neg).kinds());
    }

    /** {@code Decimal} negation only flips a sign, so it never leaves the scale a
     *  {@code +}/{@code -}/{@code *} could — total, unlike {@code Int}'s. */
    @Test
    void decimalNegationNeverAborts() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "negatesDecimal");

        Core.Neg neg = onlyOneOf(Core.Neg.class, body);

        assertTrue(program.abortsAt(neg).isEmpty());
    }

    /** {@code Rational} negation only flips the numerator's sign, never its exponents — total, the
     *  same as {@code Decimal}'s. Reached as an intermediate: {@code Rational} crosses no boundary,
     *  so {@code -(a / b)} is narrowed back to {@code Int} by the {@code toInt} it feeds. */
    @Test
    void rationalNegationNeverAborts() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "negatesRational");

        Core.Neg neg = onlyOneOf(Core.Neg.class, body);

        assertTrue(program.abortsAt(neg).isEmpty());
    }

    /**
     * {@code Int / Int} runs through {@code RationalMath.divideWholeNumbers} on two freshly-widened,
     * compact operands, so a zero divisor is the only reason this site can end without a value for
     * — never {@link AbortKind#REQUIRED_FORM_HAS_NO_PLACE}, even though the answer is
     * {@code Rational} the same way every {@code /} answers is.
     */
    @Test
    void intDividedByIntAbortsOnlyOnAZeroDivisor() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "dividesIntByInt");

        Core.Binary quotient = onlyOneOf(Core.Binary.class, body);

        assertEquals(Set.of(AbortKind.DIVISION_BY_ZERO), program.abortsAt(quotient).kinds());
    }

    /** {@code Decimal / Decimal} is the same story: both operands are widened fresh through
     *  {@code RationalMath.fromDecimal}, so only a zero divisor reaches this site. */
    @Test
    void decimalDividedByDecimalAbortsOnlyOnAZeroDivisor() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "dividesDecimalByDecimal");

        Core.Binary quotient = onlyOneOf(Core.Binary.class, body);

        assertEquals(Set.of(AbortKind.DIVISION_BY_ZERO), program.abortsAt(quotient).kinds());
    }

    /**
     * {@code (a / b) / c}: the inner {@code Int / Int} is zero-only, exactly as above, but the
     * outer division's left operand is already {@code Rational} — carrying whatever exponents the
     * inner quotient left it with — so that site adds
     * {@link AbortKind#REQUIRED_FORM_HAS_NO_PLACE}. Two {@code Core.Binary(DIV, ...)} nodes in one
     * body, told apart by which one, answering differently — the reason this classification reads
     * operand types at all rather than the shared answer type alone.
     */
    @Test
    void aDivisionWithAnAlreadyRationalOperandAlsoRisksAnAnswerWithNoPlace() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "dividesWithARationalOperand");

        List<Core.Binary> divisions = new ArrayList<>();
        for (Core node : everyNodeOf(body)) {
            if (node instanceof Core.Binary binary && binary.op() == BinOp.DIV) {
                divisions.add(binary);
            }
        }
        assertEquals(2, divisions.size(), () -> "one inner and one outer division: " + divisions);

        Core.Binary inner = null;
        Core.Binary outer = null;
        for (Core.Binary division : divisions) {
            if (division.left().type() == Type.RATIONAL) {
                outer = division;
            } else {
                inner = division;
            }
        }

        assertEquals(Set.of(AbortKind.DIVISION_BY_ZERO), program.abortsAt(inner).kinds(),
                "the inner Int / Int, same as intDividedByIntAbortsOnlyOnAZeroDivisor");
        assertEquals(Set.of(AbortKind.DIVISION_BY_ZERO, AbortKind.REQUIRED_FORM_HAS_NO_PLACE),
                program.abortsAt(outer).kinds(),
                "the outer division, whose left operand is already Rational");
    }

    @Test
    void unreachableAbortsForTheOneReasonItIs() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "unreached");

        Core.Unreachable reached = onlyOneOf(Core.Unreachable.class, body);

        assertEquals(Set.of(AbortKind.UNREACHABLE_REACHED), program.abortsAt(reached).kinds());
    }

    /** And an ordinary read never does — a program is not every site answering the same thing. */
    @Test
    void aReadOfAParameterNeverAborts() {
        CheckedProgram program = program();
        Core body = bodyOf(program, "sums");

        for (Core node : everyNodeOf(body)) {
            if (node instanceof Core.Read read) {
                assertTrue(program.abortsAt(read).isEmpty(), () -> read + " never aborts on its own");
            }
        }
    }

    /**
     * A clause's condition is emitted wherever a value of its data is built, so its sites answer
     * the same question a body's do: {@code lo + 1} leaves the range an {@code Int} holds, and the
     * comparison over it does not.
     */
    @Test
    void anIntSumInAClauseAbortsWhereTheAnswerHasNoPlace() {
        CheckedProgram program = program();
        Core condition = onlyClauseOf(program, "Span");

        Core.Binary sum = null;
        for (Core node : everyNodeOf(condition)) {
            if (node instanceof Core.Binary binary && binary.op() == BinOp.ADD) {
                sum = binary;
            }
            assertTrue(!(node instanceof Core.Read read) || program.abortsAt(read).isEmpty(),
                    () -> node + " never aborts on its own");
        }

        assertEquals(Set.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE), program.abortsAt(sum).kinds());
        assertTrue(program.abortsAt(condition).isEmpty(), "the comparison itself never aborts");
    }

    /** A clause a spread takes in is answered for in the data that includes it as well. */
    @Test
    void aClauseASpreadTakesInIsAnsweredForWhereItIsTakenIn() {
        CheckedProgram program = program();
        Core condition = onlyClauseOf(program, "LabeledSpan");

        Core.Binary sum = null;
        for (Core node : everyNodeOf(condition)) {
            if (node instanceof Core.Binary binary && binary.op() == BinOp.ADD) {
                sum = binary;
            }
        }

        assertEquals(Set.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE), program.abortsAt(sum).kinds());
    }

    /**
     * A rule a behavior declares of its answer is code an output runs where the answer is held to
     * it, so its sites answer the same question: {@code value + 1} leaves the range.
     */
    @Test
    void anIntSumInAnEnsuresRuleAbortsWhereTheAnswerHasNoPlace() {
        CheckedProgram program = program();
        CheckedBehavior bounded = null;
        for (CheckedBehavior behavior : program.module("demo").behaviors()) {
            if (behavior.name().name().equals("bounded")) {
                bounded = behavior;
            }
        }
        assertNotNull(bounded, "no behavior `bounded` in the fixture");
        List<Contract.Rule> rules = bounded.ensures().contract().rules();
        assertEquals(1, rules.size(), () -> "one rule, and " + rules);

        Core.Binary sum = null;
        for (Core node : everyNodeOf(rules.getFirst().condition())) {
            if (node instanceof Core.Binary binary && binary.op() == BinOp.ADD) {
                sum = binary;
            }
        }

        assertEquals(Set.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE), program.abortsAt(sum).kinds());
    }

    private static Core onlyClauseOf(CheckedProgram program, String data) {
        for (CheckedData declared : program.module("demo").data()) {
            if (declared.name().name().equals(data)
                    && declared instanceof CheckedData.WithFields fields) {
                assertEquals(1, fields.invariants().size(), () -> data + " holds one clause");
                return fields.invariants().getFirst().condition();
            }
        }
        throw new AssertionError("no data `" + data + "` with fields in the fixture");
    }

    /** A node this program never handed over is refused rather than answered as total. */
    @Test
    void aSiteNoProgramHandedOverIsRefused() {
        CheckedProgram program = program();
        Core.Int stray = new Core.Int(1, Type.INT, new SourcePos(1, 1));

        assertThrows(IllegalArgumentException.class, () -> program.abortsAt(stray));
    }

    private static <T extends Core> T onlyOneOf(Class<T> kind, Core body) {
        T found = null;
        for (Core node : everyNodeOf(body)) {
            if (kind.isInstance(node)) {
                if (found != null) {
                    throw new AssertionError("more than one " + kind.getSimpleName() + " in " + body);
                }
                found = kind.cast(node);
            }
        }
        if (found == null) {
            throw new AssertionError("no " + kind.getSimpleName() + " in " + body);
        }
        return found;
    }
}
