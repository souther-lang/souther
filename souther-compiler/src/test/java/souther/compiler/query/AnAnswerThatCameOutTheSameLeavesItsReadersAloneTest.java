package souther.compiler.query;

import souther.compiler.meta.ModulePath;
import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a check and a reading of an input came to again is what they came to, so what read them is
 * left alone.
 *
 * <p>The other half of what an equality is for. That two of these can be compared as values is
 * {@link EverythingAnAnswerHoldsMeansSomethingTest}'s, and it is a property of the answers; that
 * comparing them stops work is a property of the store, which keeps an answer's revision where it
 * was when the answer it replaces means the same thing. Held apart, an answer could compare equal
 * and still cost every reader a run — and no check of what the compiler says would see it.
 *
 * <p>The edit is a declaration nothing names. It reaches the module, so what is asked of the module
 * is asked again; it says nothing about any behavior, so what a check emits and what a reading of an
 * input finds are what they were. Which is the shape this is about: work that ran and came to what
 * it came to before.
 *
 * <p>"Not recomputed" is the same answer object coming back, which is how {@link
 * IncrementalCompilationTest} reads it: the store hands out what it kept, so another instance is
 * work that ran again.
 */
class AnAnswerThatCameOutTheSameLeavesItsReadersAloneTest {

    private static final String MODULE = """
            module shop.orders exposing ( twice )

            behavior twice : (n: Int) -> Int
            let twice (n) = n * 2

            example twice
                | "one" : (1) -> 2
            """;

    /** The same module and a declaration nothing names. */
    private static final String AND_SOMETHING_NOBODY_NAMES = MODULE + """

            data Unused = { a: Int }
            """;

    private static Compilation started() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("orders.sou", MODULE);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.measure(Adequacy.Asked.fullReport());
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(),
                () -> "the module compiles to begin with: " + c.db().allReports());
        return c;
    }

    private static void edited(Compilation c) {
        c.update(Map.of("orders.sou", AND_SOMETHING_NOBODY_NAMES), Set.of());
        c.measure(Adequacy.Asked.fullReport());
        c.answerEverything();
    }

    /**
     * A check that came out the same leaves what reads it alone.
     *
     * <p>What reads it here is the claims a report prints, which reads the check and nothing else —
     * so its answer coming back unchanged is the check's equality and not somebody else's.
     */
    @Test
    void aCheckThatCameOutTheSameLeavesItsReaderAlone() {
        Compilation c = started();
        Answer<Bodies.Elaborated> checked = c.db().ask(new Bodies.Checked("shop.orders"));
        Answer<?> claimed = c.db().ask(new Bodies.Claimed("shop.orders"));

        edited(c);

        Answer<Bodies.Elaborated> again = c.db().ask(new Bodies.Checked("shop.orders"));
        assertNotSame(checked, again, "the edit reached the check, so it ran again");
        assertEquals(checked, again, "and a module whose bodies are untouched checks to the same");
        assertSame(claimed, c.db().ask(new Bodies.Claimed("shop.orders")),
                "what a report says about a claim is read off that check, which said what it said");
    }

    /**
     * And a reading of an input came out the same.
     *
     * <p>Without a reader of its own here, because it has none that reads only it: every measure
     * that takes a denominator from this reading also reads the module's shapes and its check, and
     * an edit that reaches the reading reaches those. So what is held to is the reading, and what it
     * buys is that a measure asking again is a measure that finds the same denominator rather than
     * one that has to be told the answer moved.
     */
    @Test
    void aReadingOfAnInputThatCameOutTheSame() {
        Compilation c = started();
        Answer<?> inputs = c.db().ask(new Adequacy.Inputs("shop.orders"));

        edited(c);

        Answer<?> again = c.db().ask(new Adequacy.Inputs("shop.orders"));
        assertNotSame(inputs, again, "the edit reached the reading, so it ran again");
        assertEquals(inputs, again,
                "and an input nothing was said about is read to the same positions");
    }
}
