package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The number an operation answers is read by at most one representation.
 *
 * <p>At most, and the name says so. Nothing read is ordinary — most of what the library answers is
 * read by nothing at all — and where a reading is owed it is a range that says so, which is a
 * different proposition asked in {@link AnOperationTheLibraryGainsIsAnsweredForTest}. Named for one
 * rather than for at most one, this would read as the stronger claim with an exception in it, and
 * the way to make the name true would be to pull the obligation in here, where it would hold as far
 * as nothing in particular.
 *
 * <p>A term standing for a call, the form its result is of its arguments, the arithmetic it
 * computes, the body the language writes out — each is an account of the same number, and two of
 * them at one call is not two opinions but a report whose content depends on which reader arrived.
 * {@code Decimal.fromInt(n)} declared as a term as well as a form would be {@code n} to a check
 * reading forms and an opaque number to a check reading terms.
 *
 * <p>Held of every operation the library declares and not of the ones some question asks about. The
 * exclusivity is a property of the declarations, so a range that moved would move what is exclusive
 * with it — and the operations no question asks about today are exactly the ones nobody would think
 * to check by hand.
 *
 * <p>That each account is found where it is declared is not asked here either. This is a negative
 * property and stays one: an arm the resolver stopped reading would leave the operations that carry
 * it read by nothing, which is a state this is written to allow. What holds the accounts to being
 * found is {@link NumericReadingsFindTheAccountsTheLibraryDeclaresTest}.
 */
class ANumberIsReadByAtMostOneRepresentationTest {

    @Test
    void noOperationsNumberIsReadByTwoRepresentations() {
        List<String> twice = new ArrayList<>();
        for (Map.Entry<ValueName.Stdlib.Operation, Stdlib.Entry> e
                : DefaultStdlib.get().entries().entrySet()) {
            ValueName operation = e.getKey();
            NumericReadings.Resolution read = NumericReadings.resolve(
                    DefaultStdlib.get(), OperationFacts.declarations(), operation);
            if (read instanceof NumericReadings.Resolution.Multiple) {
                // Named by whatever names them in a refusal, so what a reader is told here and what
                // the library is refused with are one sentence rather than two that drift.
                twice.add(e.getKey() + " — " + NumericReadings.describe(read));
            }
        }
        assertEquals(List.of(), twice,
                "the number each of these answers is read by more than one representation, so which"
                        + " reading a report shows is whichever reader arrived");
    }
}
