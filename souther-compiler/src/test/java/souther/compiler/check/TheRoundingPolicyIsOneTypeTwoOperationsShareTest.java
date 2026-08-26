package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * {@code Decimal.round} and {@code Decimal.divide} take one rounding policy between them.
 *
 * <p>The invariant the check rests on, said where a reader can find it. Nothing in this compiler
 * names the policy type: a rule says a position of {@code Decimal.divide} reads one, and which type
 * that is comes from the argument {@code Decimal.round} declares for the same job
 * ({@code DischargeRules}). Two declarations held to each other, which is a check only while they
 * really are two declarations of one thing.
 *
 * <p>So this is the sentence that reading assumes. Either operation moving to a policy of its own
 * fails the build where the facts are registered, which is a class initializer and says nothing
 * about an anchor; this fails first and says what the anchor is.
 *
 * <p>Both moving together passes here and there, and should: that is the library choosing a new
 * policy type, not the hand-written arithmetic and the library disagreeing.
 */
class TheRoundingPolicyIsOneTypeTwoOperationsShareTest {

    private static final ValueName.Stdlib.Operation ROUND =
            ValueName.Stdlib.operation("Decimal", "round");

    private static final ValueName.Stdlib.Operation DIVIDE =
            ValueName.Stdlib.operation("Decimal", "divide");

    /** {@code divide(dividend, divisor, scale, mode)}. */
    private static final int MODE_OF_DIVIDE = 3;

    /** {@code round(scale, mode, d)}. */
    private static final int MODE_OF_ROUND = 1;

    @Test
    void theTypeEachTakesForItIsTheSameType() {
        assertEquals(argumentOf(ROUND, MODE_OF_ROUND),
                argumentOf(DIVIDE, MODE_OF_DIVIDE),
                "the arithmetic over a rounded quotient is held to the policy `Decimal.round`"
                        + " declares, so a policy of its own would hold `Decimal.divide` to nothing");
    }

    /** And it is a declaration, rather than a number or a scalar that happens to sit there. */
    @Test
    void andItIsATypeSomethingDeclares() {
        assertEquals(Type.Ref.class, argumentOf(ROUND, MODE_OF_ROUND).getClass(),
                "a policy is a declared type; a scale is the count beside it");
        assertEquals(Type.INT, argumentOf(ROUND, 0),
                "and the scale is that count");
    }

    private static Type argumentOf(ValueName.Stdlib.Operation operation, int at) {
        Stdlib.Entry entry = DefaultStdlib.get().entry(operation);
        assertNotNull(entry, () -> "the library declares no `" + operation + "`");
        assertEquals(true, entry.signature().params().size() > at,
                () -> "`" + operation + "` takes " + entry.signature().params().size()
                        + " argument(s), and this reads " + (at + 1));
        return entry.signature().params().get(at);
    }
}
