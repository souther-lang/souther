package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which operations the library writes are read through their body where the analysis reads a tree
 * of meanings.
 *
 * <p>A helper that has a fact stated of it, hands its closure something or calls another operation
 * stays a call, since a reader of that fact or of that walk looks for the call. The set read through
 * is held here so that a helper added to the library is read through on purpose.
 */
class WhichLibraryHelpersTheAnalysisReadsThroughTest {

    @Test
    void onlyAnOptionConsumedInOneMatchIsReadThrough() {
        Set<String> readThrough = LibraryReadThrough.shipped().stream()
                .map(ValueName.Stdlib.Operation::toString).collect(Collectors.toSet());

        assertEquals(Set.of("Option.withDefault"), readThrough);
    }

    /** The shipped table is the function of the shipped library and facts, and no more. */
    @Test
    void theShippedTableIsWhatTheLibraryAndItsFactsComeTo() {
        assertEquals(LibraryReadThrough.shipped(), LibraryReadThrough.of(DefaultStdlib.get(),
                DefaultBoundOperationFacts.get()));
    }

    /** A library other than the shipped one is read against facts bound to it, and a copy of the
     *  shipped sources comes to what the shipped library does. */
    @Test
    void anotherLibraryIsReadAgainstItsOwnFacts() {
        Stdlib another = StdlibLoader.load();

        assertNotSame(DefaultStdlib.get(), another);
        assertEquals(LibraryReadThrough.shipped(), LibraryReadThrough.of(another));
    }

    /** What a fact is stated of is held as a call, whatever its body is. */
    @Test
    void anOperationWithAFactStaysACall() {
        ValueName.Stdlib.Operation max = ValueName.Stdlib.operation("Int", "max");

        assertTrue(DefaultBoundOperationFacts.get().statesAnythingOf(max));
        assertTrue(!LibraryReadThrough.shipped().contains(max));
    }
}
