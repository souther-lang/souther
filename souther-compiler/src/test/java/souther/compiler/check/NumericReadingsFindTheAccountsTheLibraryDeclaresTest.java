package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Each account of a number is found where the library declares it.
 *
 * <p>What the invariant beside this cannot say. That one refuses a second reading, so it is asked of
 * an operation by counting to more than one — and an arm the resolver stopped reading takes its
 * operations from one reading to none, which is a state that invariant exists to allow. Measured:
 * with the arm for the arithmetic an operation computes removed, the whole suite stayed green.
 *
 * <p>So an account nobody reads and an account nobody looked for were the same observation, which is
 * the defect the questions exist against, one level up. Here each arm is named at an operation that
 * carries it, so a reading that stops being found is a failure rather than an operation that turns
 * out to have none.
 *
 * <p>One operation per arm and no more. This is a characterization of the resolver and not a table
 * of the library: what every operation answers is asked of the declarations themselves, and a list
 * kept here would be a second copy of them, wrong one turn later.
 */
class NumericReadingsFindTheAccountsTheLibraryDeclaresTest {

    @Test
    void aTermIsFoundWhereOneIsDeclared() {
        assertInstanceOf(NumericReading.AsATermTakenOfItsArgument.class,
                readingOf("List.length"),
                "List.length is declared to answer a number taken of the one value it is given");
    }

    @Test
    void aFormIsFoundWhereOneIsDeclared() {
        assertInstanceOf(NumericReading.AsAFormOfItsArguments.class,
                readingOf("Decimal.fromInt"),
                "Decimal.fromInt is declared to answer the count of its argument");
    }

    @Test
    void theArithmeticAnOperationComputesIsFound() {
        assertInstanceOf(NumericReading.AsTheArithmeticItComputes.class,
                readingOf("Int.add"),
                "Int.add is declared to compute the arithmetic the operator stands for");
    }

    @Test
    void aBodyTheLanguageWritesOutIsFound() {
        assertInstanceOf(NumericReading.ByTheBodyTheLanguageWritesOut.class,
                readingOf("Int.abs"),
                "Int.abs is an ordinary let, so what it answers is read by reading it");
    }

    /**
     * And an operation answering no number carries no account of one.
     *
     * <p>{@code Date.addDays} declares a form and answers a date. The form is about what its
     * arguments are counted as, which is what lets a date take part in one at all; it is not an
     * account of a number the operation answered, because it answered none. Counted as one, every
     * such operation would carry a reading whose subject is missing — and a proposition with no
     * subject cannot come out false, so the count would look right for the wrong reason.
     */
    @Test
    void anOperationThatAnswersNoNumberCarriesNoAccountOfOne() {
        assertEquals(new NumericReadings.Resolution.None(), resolutionOf("Date.addDays"),
                "a form over what its arguments are counted as is not a reading of a number this"
                        + " operation answers, since it answers a date");
    }

    private static NumericReading readingOf(String qualified) {
        NumericReadings.Resolution resolved = resolutionOf(qualified);
        return assertInstanceOf(NumericReadings.Resolution.One.class, resolved,
                qualified + " carries one account of the number it answers, and this is what was"
                        + " found instead").reading();
    }

    private static NumericReadings.Resolution resolutionOf(String qualified) {
        ValueName operation = DefaultStdlib.get().operation(qualified);
        return NumericReadings.resolve(
                DefaultStdlib.get(), OperationFacts.declarations(), operation);
    }
}
