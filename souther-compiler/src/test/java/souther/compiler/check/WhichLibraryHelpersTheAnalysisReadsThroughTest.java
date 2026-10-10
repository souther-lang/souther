package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.types.ValueName;

import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

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
        Set<String> readThrough = HelperTable.transparentIn(DefaultStdlib.get()).stream()
                .map(ValueName.Stdlib.Operation::toString).collect(Collectors.toSet());

        assertEquals(Set.of("Option.withDefault"), readThrough);
    }

    @Test
    void theSetIsWorkedOutOncePerLibrary() {
        assertSame(HelperTable.transparentIn(DefaultStdlib.get()),
                HelperTable.transparentIn(DefaultStdlib.get()));
    }
}
