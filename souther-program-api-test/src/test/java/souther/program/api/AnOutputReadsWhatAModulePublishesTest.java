package souther.program.api;

import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.Exposure;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a module publishes, as an output reads it.
 *
 * <p>An output decides what its artifact says about a name it emits — public or not on the JVM, a
 * symbol the linker sees or one it does not in an object — and that decision is the module's
 * {@code exposing} clause and nothing else. An output working it out for itself would publish a
 * surface the module never stated, and the only other route is reading the source again, which is
 * the re-derivation this boundary exists to stop.
 */
class AnOutputReadsWhatAModulePublishesTest {

    private static final String WITH_A_CLAUSE = """
            module pricing exposing ( total )

            behavior total : (a: Int) -> Int
            let total (a) = kept(a)

            behavior kept : (a: Int) -> Int
            let kept (a) = a + 1
            """;

    /** A module with no clause publishes everything, and says so rather than answering nothing. */
    private static final String WITH_NONE = """
            module plainly

            behavior one : (a: Int) -> Int
            let one (a) = a

            behavior other : (a: Int) -> Int
            let other (a) = a
            """;

    @Test
    void aNameTheClauseListsIsPublishedAndOneItDoesNotIsKept() {
        CheckedModule module = CheckedProgram.of(List.of(WITH_A_CLAUSE)).module("pricing");

        assertEquals(Exposure.EXPOSED, exposureOf(module, "total"));
        assertEquals(Exposure.KEPT, exposureOf(module, "kept"));
    }

    @Test
    void aModuleWithNoClausePublishesEveryNameItDeclares() {
        CheckedModule module = CheckedProgram.of(List.of(WITH_NONE)).module("plainly");

        assertEquals(Exposure.EXPOSED, exposureOf(module, "one"));
        assertEquals(Exposure.EXPOSED, exposureOf(module, "other"));
    }

    private static Exposure exposureOf(CheckedModule module, String name) {
        for (CheckedBehavior behavior : module.behaviors()) {
            if (behavior.name().name().equals(name)) {
                return behavior.exposure();
            }
        }
        throw new AssertionError(module.name() + " declares no behavior " + name);
    }
}
