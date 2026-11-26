package souther.compiler.examples;

import souther.compiler.generated.GeneratedImplementations;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An implementation this compile emitted and cannot reach is said where it is applied, and not as a
 * stand-in that could not be made.
 *
 * <p>The constructor is read before any stand-in is made, because what a stand-in has to be is what
 * the constructor takes. Reading it is where an implementation not in the classes is found, and that
 * is before the half of the seam a stand-in that could not be made is raised in — so moved there as
 * it stands, a row reaching no implementation would be said to have had no environment.
 */
class AnImplementationOutOfReachIsSaidWhereItIsAppliedTest {

    @Test
    void anImplementationNotInTheClassesIsNotReachedWhenApplied() {
        GeneratedImplementation answerer = new GeneratedImplementation(
                new GeneratedImplementations("probe.gone", Set.of("top"), Set.of()),
                new MemoryClassLoader(Map.of(), getClass().getClassLoader()));
        Answerer.Answer.Something top =
                assertInstanceOf(Answerer.Answer.Something.class, answerer.of("top"));
        DependencyStandin convert = new DependencyStandin(
                new ValueName.Behavior("probe.gone", "convert"), _ -> 1L);

        Answerer.Applying applying = assertDoesNotThrow(() -> top.applying(List.of(convert)),
                "no stand-in was wrong, so none is said to have been");
        assertThrows(ImplementationNotReached.class, () -> applying.to(List.of()));
    }
}
