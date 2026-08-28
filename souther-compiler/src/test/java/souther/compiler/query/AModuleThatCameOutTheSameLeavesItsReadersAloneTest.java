package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;

/**
 * What a module compiles to is a value, so a generation that ran again and came to the same class
 * files leaves what read it alone.
 *
 * <p>The store decides what to recompute by comparing an answer with the one it replaces, and a
 * module's classes were a map of arrays: an array is the array it is whatever it holds, so such an
 * answer never equalled its own recomputation. Every example in the workspace reads some module's
 * classes, so a module regenerated to the very same bytes reached all of them, on every revision,
 * and nothing about what the compiler said could see it.
 *
 * <p>Asked of the classes and not of any one reader. What a reader does with an answer that came out
 * the same is {@link AnAnswerThatCameOutTheSameLeavesItsReadersAloneTest}'s, over the store's own
 * rule; what is here is that this answer is one the rule can act on.
 */
class AModuleThatCameOutTheSameLeavesItsReadersAloneTest {

    private static final String SOURCE = """
            module demo
            data In = { n: Int }
            data Out = { n: Int }
            behavior twice : (i: In) -> Out
            let twice (i) = Out { n = i.n * 2 }
            """;

    private static final String OTHERWISE = SOURCE.replace("i.n * 2", "i.n * 3");

    /**
     * Two compiles of one source come to one program.
     *
     * <p>Nothing of the store in it: two generations build their own arrays and always did, and what
     * this asks is whether what holds them says the two runs came to the same thing. Everything
     * below rests on it.
     */
    @Test
    void twoCompilesOfOneSourceComeToOneProgram() {
        Map<String, ClassFileImage> first = Compiler.compile(SOURCE);
        Map<String, ClassFileImage> second = Compiler.compile(SOURCE);

        assertFalse(first.isEmpty(), "there are classes to compare");
        assertNotSame(first, second, "two compiles, so two maps");
        assertEquals(first, second, "and one program");
    }

    /** And two sources that say different things do not, so the row above is not equality on
     *  everything. */
    @Test
    void andTwoSourcesThatSayDifferentThingsDoNot() {
        assertNotEquals(Compiler.compile(SOURCE), Compiler.compile(OTHERWISE));
    }

    /**
     * A module regenerated to what it already was is the program that was already there.
     *
     * <p>Driven through an edit and its undo with the classes asked in between, which is what makes
     * the generation run a second time: the store keeps the edited answer, going back differs from
     * it, and everything from the parse down is worked out again. The map that comes back is a new
     * map — that is what {@code assertNotSame} says — and what it holds is the program from before
     * the edit, which is what the store compares and what lets it stop.
     */
    @Test
    void aModuleRegeneratedToWhatItWasIsTheProgramThatWasThere() {
        Compilation compilation = Compilation.ofDocuments(
                Map.of("a.sou", SOURCE), Set.of(), ModulePath.EMPTY);
        Answer<Map<String, ClassFileImage>> before = compilation.db().ask(new Output.All());

        compilation.update(Map.of("a.sou", OTHERWISE), Set.of());
        Answer<Map<String, ClassFileImage>> edited = compilation.db().ask(new Output.All());
        assertNotEquals(before.value(), edited.value(), "the edit reached the classes");

        compilation.update(Map.of("a.sou", SOURCE), Set.of());
        Answer<Map<String, ClassFileImage>> undone = compilation.db().ask(new Output.All());

        assertNotSame(before, undone, "the generation ran again");
        assertEquals(before, undone, "and came to the program that was there");
    }
}
