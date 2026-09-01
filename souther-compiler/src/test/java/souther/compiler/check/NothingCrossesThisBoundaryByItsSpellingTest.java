package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What one representation becomes in the next is written down, never read off a name.
 *
 * <p>{@code Resolve} is where the parsed tree becomes what the rest of the compiler gives a meaning
 * to, and several of the vocabularies on the two sides are closed: an operator, the kind of a
 * primitive Raw. Each such crossing is a decision about what a written thing denotes, and this pass
 * makes it in an exhaustive switch that names both sides. Taking the answer from
 * {@code valueOf(x.name())} instead makes it a shared spelling, and a spelling is not a decision:
 * extend both enums with the same name and the translation goes on quietly, having decided nothing.
 *
 * <p>The rule this stands for is that this pass does not infer one closed representation from
 * another one's spelling. What is checked is stricter: the word {@code valueOf} does not appear in
 * the pass at all. The word and not a call written a particular way — a call is one of the shapes
 * the word comes in, beside {@code valueOf (x)}, beside {@code BinOp::valueOf} handed to something
 * that applies it, and beside {@code Enum.valueOf(BinOp.class, ...)}. Each of those is the same
 * thing asked for, and a check that named the shape in front of it would be one the next shape
 * walks past. It costs nothing today, because translating by name was the only thing this pass used
 * the word for.
 *
 * <p>Being stricter than the rule, it can refuse something the rule allows —
 * {@code Denotations.valueOf(BindingId)}, next door in this package, is a lookup and no crossing at
 * all. That is the check working as designed and not a miss in it. Should such a call become
 * necessary here, decide about this check itself: narrowing it to the enums known today puts the
 * hole back, since what it is here for is the crossing nobody has written yet.
 */
class NothingCrossesThisBoundaryByItsSpellingTest {

    /** The pass that holds the boundary, and so the one this is about. */
    private static final Path RESOLVE = Path.of("src/main/java/souther/compiler/check/Resolve.java");

    @Test
    void resolveTranslatesByDecidingRatherThanByReadingAName() throws IOException {
        assertTrue(Files.isRegularFile(RESOLVE), () -> "no " + RESOLVE.toAbsolutePath());
        String text = Files.readString(RESOLVE);

        assertEquals(0, occurrences(text, "valueOf"),
                "a closed vocabulary crosses this boundary in a switch that names both sides, so"
                        + " that adding to what may be written stops the compile until somebody says"
                        + " what it denotes; a name the two sides happen to share says nothing about"
                        + " that. A valueOf that is a lookup rather than a crossing is refused here"
                        + " too — decide about this check, do not narrow it to the enums of the day");
    }

    private static int occurrences(String text, String word) {
        int count = 0;
        for (int at = text.indexOf(word); at >= 0; at = text.indexOf(word, at + word.length())) {
            count++;
        }
        return count;
    }
}
