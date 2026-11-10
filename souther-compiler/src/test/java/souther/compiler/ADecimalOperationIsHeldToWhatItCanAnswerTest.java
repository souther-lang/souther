package souther.compiler;

import souther.runtime.ConstraintViolation;
import souther.runtime.OutOfRoom;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A Decimal operation answers the value the model wrote or the run fails, and what it cannot do is
 * answer a different one (spec §a-scale-is-used-as-the-number-written).
 *
 * <p>Two shortages, and they are told apart. A scale is an {@code Int}, which is 64 bits, and what a
 * {@code BigDecimal} divides at is 32; a scale outside those cannot be handed over as the number it
 * is. A scale that can be handed over may still name an answer with more digits than the host
 * builds, which every one of these operations can ask for — a sum and a product included, the
 * product first, since a product's scale is the sum of its factors'. Both answers are decimals, and
 * neither is the model's fault: each reaches a boundary as {@code OutOfRoom} (spec §jvm-abort), the
 * platform failing, and never as {@code java.lang.ArithmeticException}, a {@code java.math} type
 * named in the failure of a program that has no such type. A value no {@code Int} holds is the one
 * refusal here, and it is the language's ({@code ConstraintViolation}).
 */
class ADecimalOperationIsHeldToWhatItCanAnswerTest {

    private static final String MODULE = """
            module demo

            data In = { a: Decimal, b: Decimal, s: Int }
            data Out = { value: Decimal, ok: Bool }

            behavior divv : (i: In) -> Out constructs Out
            let divv (i) =
                match Decimal.divide(i.a, i.b, i.s, HALF_UP) with
                    | Decimal as q -> Out { value = q, ok = true }
                    | DivisionByZero -> Out { value = i.a, ok = false }

            behavior rnd : (i: In) -> Out constructs Out
            let rnd (i) = Out { value = Decimal.round(i.s, HALF_UP, i.a), ok = true }

            behavior times : (i: In) -> Out constructs Out
            let times (i) = Out { value = i.a * i.b, ok = true }

            behavior plus : (i: In) -> Out constructs Out
            let plus (i) = Out { value = i.a + i.b, ok = true }

            // The scale argument is an expression that aborts, so whether it ran is observable.
            behavior divvAborting : (i: In) -> Out constructs Out
            let divvAborting (i) =
                match Decimal.divide(i.a, i.b, Decimal.toInt(HALF_UP, i.a), HALF_UP) with
                    | Decimal as q -> Out { value = q, ok = true }
                    | DivisionByZero -> Out { value = i.a, ok = false }
            """;

    /** A Decimal no Int holds, so `Decimal.toInt` of it aborts (spec §stdlib-decimal). */
    private static final BigDecimal PAST_AN_INT = new BigDecimal("99999999999999999999");

    /** A scale at the far end of what a {@code BigDecimal} keeps its scale in. Every operation given
     *  one has a result too long to hold, and none of them narrows it to get there. */
    private static final BigDecimal TINY = new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE);

    private static BytesClassLoader loaded() {
        return new BytesClassLoader(Compiler.compile(MODULE),
                ADecimalOperationIsHeldToWhatItCanAnswerTest.class.getClassLoader());
    }

    private static Map<?, ?> run(BytesClassLoader loader, String behavior,
                                 BigDecimal a, BigDecimal b, long scale) throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", Map.of("a", a, "b", b, "s", scale));
        Object beh = Emitted.behavior(loader, "demo", behavior).getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(beh, in));
    }

    /** What {@code behavior} ends with on these arguments, which is a {@code failure}. */
    private static <T extends Throwable> T fails(Class<T> failure, BytesClassLoader loader,
                                                 String behavior, BigDecimal a, BigDecimal b,
                                                 long scale) {
        Throwable raised = assertThrows(Throwable.class,
                () -> run(loader, behavior, a, b, scale));
        Throwable at = raised;
        while (at.getCause() != null && !failure.isInstance(at)) {
            at = at.getCause();
        }
        assertTrue(failure.isInstance(at),
                behavior + " raised " + at.getClass().getName() + ": " + at.getMessage());
        return failure.cast(at);
    }

    private static OutOfRoom shortOfRoom(BytesClassLoader loader, String behavior,
                                         BigDecimal a, BigDecimal b, long scale) {
        return fails(OutOfRoom.class, loader, behavior, a, b, scale);
    }

    @Test
    void aScaleTheRunTimeTakesDividesAtTheScaleThatWasWritten() throws Exception {
        BytesClassLoader loader = loaded();
        assertEquals(new BigDecimal("2.33"),
                run(loader, "divv", new BigDecimal("7"), new BigDecimal("3"), 2L).get("value"));
    }

    /**
     * {@code 4294967298} is {@code 2 + 2^32}, so a narrowing that drops the high bits leaves 2 —
     * which is a scale a model might well have written, and the answer at it is a well-formed
     * Decimal. Nothing downstream could have told the two apart.
     */
    @Test
    void aScaleNoIntHoldsIsShortOfRoomRatherThanDividingAtTheScaleTheLowBitsSpell() {
        BytesClassLoader loader = loaded();
        for (String behavior : new String[] {"divv", "rnd"}) {
            OutOfRoom e = shortOfRoom(loader, behavior, new BigDecimal("7"), new BigDecimal("3"),
                    4294967298L);
            assertTrue(e.getMessage().contains("4294967298"), e.getMessage());
            assertTrue(e.getMessage().contains("scale"), e.getMessage());
        }
    }

    /** The same the other way: {@code -2^32} narrows to 0, which divides to a whole number. */
    @Test
    void aNegativeScaleNoIntHoldsIsShortOfRoomToo() {
        BytesClassLoader loader = loaded();
        for (String behavior : new String[] {"divv", "rnd"}) {
            OutOfRoom e = shortOfRoom(loader, behavior, new BigDecimal("7"), new BigDecimal("3"),
                    -4294967296L);
            assertTrue(e.getMessage().contains("-4294967296"), e.getMessage());
        }
    }

    /**
     * A scale an {@code int} holds exactly, and a division at it with more digits than the host
     * builds. The message must not call this a scale past what is taken: the scale was handed over
     * as the number it is, and what was short is room for the answer at it.
     */
    @Test
    void aScaleHandedOverExactlyIsStillShortOfRoomWhereTheAnswerIsTooLongToWrite() {
        BytesClassLoader loader = loaded();
        for (String behavior : new String[] {"divv", "rnd"}) {
            OutOfRoom e = shortOfRoom(loader, behavior,
                    new BigDecimal("7"), new BigDecimal("3"), Integer.MAX_VALUE);
            assertTrue(e.getMessage().contains("no room to write"), e.getMessage());
        }
    }

    /** The operators are the same operations and are short of room the same way: no scale is
     *  written anywhere in {@code a * b}. */
    @Test
    void anOperatorRunningPastABigDecimalsScalesIsShortOfRoom() {
        BytesClassLoader loader = loaded();
        assertTrue(shortOfRoom(loader, "times", TINY, TINY, 2L).getMessage().contains("product"));
        assertTrue(shortOfRoom(loader, "plus", TINY,
                new BigDecimal(BigInteger.ONE, Integer.MIN_VALUE), 2L).getMessage().contains("sum"));
    }

    /**
     * A zero divisor answers its case whatever the scale, including one no division could have run
     * at: a division that does not run needs no scale to run at (spec
     * §a-division-that-does-not-run-needs-no-scale).
     */
    @Test
    void aZeroDivisorIsAnsweredBeforeTheScaleIs() throws Exception {
        BytesClassLoader loader = loaded();
        for (long scale : new long[] {2L, 4294967298L, Integer.MAX_VALUE}) {
            assertEquals(false,
                    run(loader, "divv", new BigDecimal("7"), BigDecimal.ZERO, scale).get("ok"),
                    "scale " + scale);
        }
    }

    /**
     * Every argument of a call runs. Only {@code &&} and {@code ||} decide which of their operands
     * do (spec §a-condition-stops-when-its-answer-is-settled), so a scale expression that aborts
     * aborts whether or not the divisor turns out to be zero.
     *
     * <p>The backend used to emit this operation itself and evaluated the scale and the mode only
     * on the branch it divided on, which is a short-circuit no declaration wrote down: with a zero
     * divisor the abort below did not happen and the call answered {@code DivisionByZero}.
     */
    @Test
    void everyArgumentOfADivideRunsWhateverTheDivisorTurnsOutToBe() {
        BytesClassLoader loader = loaded();
        for (BigDecimal divisor : new BigDecimal[] {new BigDecimal("3"), BigDecimal.ZERO}) {
            ConstraintViolation e = fails(ConstraintViolation.class, loader, "divvAborting",
                    PAST_AN_INT, divisor, 2L);
            assertTrue(e.getMessage().contains("does not fit in an Int"),
                    "divisor " + divisor + ": " + e.getMessage());
        }
    }

    /**
     * Which of two invalid conditions decides the answer is a separate question from which
     * arguments run, and it is stated: a division that does not run needs no scale to run at (spec
     * §a-division-that-does-not-run-needs-no-scale). The scale expression above ran; this scale
     * value is one no division could have used, and the answer is still the case the model handles.
     */
    @Test
    void aZeroDivisorAnswersItsCaseEvenWhereTheScaleIsOneNoDivisionCouldRunAt() throws Exception {
        BytesClassLoader loader = loaded();
        assertEquals(false,
                run(loader, "divv", new BigDecimal("7"), BigDecimal.ZERO, 4294967298L).get("ok"));
    }

    /**
     * A message over a value at the end of a {@code BigDecimal}'s scales is bounded. Written with
     * {@code toPlainString()} it would spell the value out — two billion characters for a scale at
     * the end — which is the allocation the operation just had no room for, so the failure path
     * would fail.
     */
    @Test
    void aMessageDoesNotSpellOutAValueTheRunHadNoRoomToBuild() {
        BytesClassLoader loader = loaded();
        String said = shortOfRoom(loader, "times", TINY, TINY, 2L).getMessage();
        assertTrue(said.length() < 200, "message is " + said.length() + " characters");
        assertTrue(said.contains("scale " + Integer.MAX_VALUE), said);
    }
}
