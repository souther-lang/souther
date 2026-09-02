package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Kernel;
import souther.compiler.core.KernelSignature;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Every library operation that answers something about a string is one somebody decided about.
 *
 * <p>What {@link StringPredicates} holds is which operations say which strings stand at a position.
 * A predicate the table does not hold is a rule that reaches the readings as a form none of them
 * takes apart — the position admits every string there is, no value can be composed for it, and
 * what that costs is a field two lines away losing an obligation nothing about it changed
 * (issue #1249). Which is a thing to decide about a new predicate, and was a thing nobody was asked
 * to decide.
 *
 * <p><b>The candidates come from the library and the judgment does not.</b> An operation answering
 * a {@code Bool} about a {@code String} is where such a rule can come from, and that is read off
 * the declared signatures rather than off a list somebody keeps. What it is not is a classification:
 * some of these say nothing a set of strings can hold, and each of those is written down below with
 * the reason. So the check is that nothing is unaccounted for, and never that the shape of a
 * signature decides what an operation means.
 */
class EveryPredicateOverAStringIsReadAsASetOfStringsTest {

    /**
     * The ones the candidate shape catches that are no predicate about a string's own characters,
     * each with why a set of strings is not what it says.
     *
     * <p>Written out, so that an operation added to the library is unaccounted for until somebody
     * says which of the two it is. A default would answer for it, and answer wrong exactly where it
     * matters — a new predicate over strings is one this reading would go on saying nothing about.
     */
    private static final Map<Kernel, String> SAY_NO_SET_OF_STRINGS = new LinkedHashMap<>();

    static {
        // Empty today: every operation the shape below catches is one whose strings are read. The
        // two checks that guard this map are what keeps it honest as it fills, and they are here
        // rather than added later because the day a row arrives is the day somebody is deciding.
    }

    /** Every operation the library declares that answers a `Bool` and reads a `String`. */
    private static List<Kernel> candidates() {
        Stdlib stdlib = DefaultStdlib.get();
        List<Kernel> out = new ArrayList<>();
        for (ValueName.Stdlib.Operation operation : stdlib.entries().keySet()) {
            Stdlib.Intrinsic intrinsic = stdlib.intrinsicOf(operation);
            if (intrinsic == null) {
                continue;
            }
            KernelSignature signature = intrinsic.signature();
            if (signature.result() == Type.BOOL
                    && signature.parameters().stream().anyMatch(each -> each == Type.STRING)
                    && !out.contains(intrinsic.kernel())) {
                out.add(intrinsic.kernel());
            }
        }
        return out;
    }

    /** There are some, so the check below is about something. */
    @Test
    void theLibraryDeclaresSuchOperations() {
        assertFalse(candidates().isEmpty(), "no operation answers a Bool about a String");
    }

    /** And each of them is read as a set of strings or is written down as one that is not. */
    @Test
    void eachOfThemIsReadOrIsWrittenDownAsOneThatIsNot() {
        List<Kernel> unaccounted = candidates().stream()
                .filter(each -> StringPredicates.of(each) == null)
                .filter(each -> !SAY_NO_SET_OF_STRINGS.containsKey(each))
                .toList();

        assertEquals(List.of(), unaccounted,
                "an operation answering a Bool about a String that nothing decided about: either"
                        + " StringPredicates says which strings it admits, or the map above says"
                        + " why a set of strings is not what it states");
    }

    /** And nothing is written down twice, which would be two answers about one operation. */
    @Test
    void nothingIsBothReadAndWrittenOff() {
        List<Kernel> both = SAY_NO_SET_OF_STRINGS.keySet().stream()
                .filter(each -> StringPredicates.of(each) != null).toList();

        assertEquals(List.of(), both, "an operation both read and said to be unreadable");
    }

    /** And nothing is written off that the candidates never reach, which would be a line nobody
     *  reads standing for a decision nobody has to make. */
    @Test
    void nothingIsWrittenOffThatIsNotACandidate() {
        List<Kernel> stale = SAY_NO_SET_OF_STRINGS.keySet().stream()
                .filter(each -> !candidates().contains(each)).toList();

        assertEquals(List.of(), stale, "a reason written for an operation this never asks about");
    }
}
