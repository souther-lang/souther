package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.Symbols;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A reading refuses a term under nothing the behavior it is of takes.
 *
 * <p>Every other question here refuses one, and what a term is measured on has to refuse it for the
 * same reason: an order follows from what stands where the number comes from, and there is nothing
 * standing anywhere for a path this input has no parameter for.
 *
 * <p><b>An answer would come back, which is why the refusal is the point.</b> What an operation
 * answers with follows from the operation for every operation whose answer does not depend on what
 * it was given — a length is a whole number whatever it is a length of — so a term of another
 * input's parameter comes back ordered on one end and blank on the other. That is an answer about no
 * reading at all, wearing the name of this one.
 */
class AReadingAnswersAboutItsOwnTermsAndNoOthersTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    /** A reading of one behavior's input, which takes a string called {@code s}. */
    private static Quantities readingOfAString() {
        return InputDomain.of(
                List.of(new InputDomain.Parameter("s", null, Type.STRING)),
                SYMBOLS, ReadAs.THE_COMPILATION_DOES).quantities(SYMBOLS);
    }

    /** A reading of another behavior's input, which takes a whole number called {@code n} and has
     *  no parameter the term below is under. */
    private static Quantities readingOfANumber() {
        return InputDomain.of(
                List.of(new InputDomain.Parameter("n", null, Type.INT)),
                SYMBOLS, ReadAs.THE_COMPILATION_DOES).quantities(SYMBOLS);
    }

    /** How long the string at {@code s} is, which is a term of the first reading. */
    private static NumericTerm lengthOfS() {
        NumericTerm.TakenOf made = NumericTerm.TakenOf.of(
                ValueName.Stdlib.operation("String", "length"), TermPath.of("s"), Type.STRING,
                SYMBOLS);
        assertNotNull(made, "a length is taken of a string");
        return made;
    }

    /** The reading it is a term of answers about it. */
    @Test
    void aTermOfThisInputIsAnswered() {
        TermOrders orders = readingOfAString().ordersOf(lengthOfS());

        assertEquals(souther.compiler.check.Carrier.WHOLE, orders.answered(),
                "a length is counted in whole numbers");
        assertEquals(souther.compiler.check.Carrier.TEXT, orders.observed(),
                "and the value it is read off is a string");
    }

    /** And a reading that takes nothing it is under refuses it rather than answering half of it. */
    @Test
    void aTermOfAnotherInputIsRefused() {
        Quantities elsewhere = readingOfANumber();
        NumericTerm foreign = lengthOfS();

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> elsewhere.ordersOf(foreign));

        assertEquals(true, refused.getMessage().contains("s"),
                "the refusal names the path nothing here takes: " + refused.getMessage());
    }

    /** What the answer would have been, which is what makes the refusal load-bearing. */
    @Test
    void theAnswerItWouldHaveGivenIsHalfOne() {
        assertEquals(souther.compiler.check.Carrier.WHOLE,
                lengthOfS().answeredOn(null, SYMBOLS),
                "the operation answers with a whole number wherever it was applied");
        assertEquals(null, lengthOfS().observedOn(null, SYMBOLS),
                "and nothing says what a value at the position is read on, since there is none");
    }
}
