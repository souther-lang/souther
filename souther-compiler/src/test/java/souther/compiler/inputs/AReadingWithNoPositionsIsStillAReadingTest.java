package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.Symbols;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A walk that found no positions comes back with a reading, and not with the absence of one.
 *
 * <p>Which is what tells the two apart everywhere else. A reading is made by walking what a
 * behavior takes, so what it found is what the input has; a caller that could not get one has
 * nothing, and there is no value of this type for it to answer with. Written down as one value
 * they were the same answer, and a behavior nobody could read the input of measured as an input
 * the model divides nowhere.
 *
 * <p>So this holds the empty one to being a reading: it says how its names are read and what it
 * was made of, the way one that found ten positions does.
 */
class AReadingWithNoPositionsIsStillAReadingTest {

    private static final String MODEL = """
            module example.nothing

            data Size = Int

            behavior size : (n: Size) -> Size
            let size (n) = n
            """;

    private static Symbols symbols() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        return Scopes.derived(compilation.db(), compilation.modules().get(0)).value();
    }

    /** Nothing to walk is not nothing walked. */
    @Test
    void aWalkOverNoParametersIsAReadingOfAnInputWithNoPositions() {
        ReadingPolicy policy = ReadAs.THE_COMPILATION_DOES;
        InputDomain read = InputDomain.of(List.of(), symbols(), policy);

        assertNotNull(read, "a walk answers with a reading");
        assertEquals(List.of(), read.positions(), "and it found no positions");
        assertEquals(List.of(), read.parameters(), "because it was given no parameters");
        assertNull(read.at(TermPath.of("n")),
                "so it has no position anywhere, which is its own answer and not a missing one");
    }

    /**
     * And it answers what it was read under.
     *
     * <p>The half a shared empty value could not hold. Standing for every absence at once it
     * belonged to no compile, so it had no policy to give, and a reader asking how the names in it
     * are read got nothing back.
     */
    @Test
    void andItSaysHowItsNamesAreRead() {
        ReadingPolicy policy = ReadAs.THE_COMPILATION_DOES;

        assertSame(policy, InputDomain.of(List.of(), symbols(), policy).policy());
    }
}
