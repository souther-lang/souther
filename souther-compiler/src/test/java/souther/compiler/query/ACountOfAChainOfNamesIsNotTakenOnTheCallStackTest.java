package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.check.TypeCardinality;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A chain of names each worn over the one before is counted one link at a time, in an order that has
 * every link answered before the link that reads it.
 *
 * <p>Every name is a component of its own and the count of one is handed what the one it wraps came
 * to. Asked as each was reached, the count at the top would wait on the one beneath it, and that one
 * on the next, so how long a chain a module could hold would be how deep a stack the thread compiling
 * it had. And a count reaching a name opens it to read what it wraps; opening every name beneath it
 * as well would read the chain once per link.
 *
 * <p>Held three ways, because each is a different place the depth could come back. On a small stack,
 * compiled once, again with nothing changed, and again after the bottom of the chain is edited —
 * since checking that a kept answer still holds asks what it read, and that is a walk of its own. In
 * what each count is recorded as reading, which is what the checking walks. And in how many names a
 * count opens, which is where the reading of the chain was paid for.
 *
 * <p>The chains are short and the stack is smaller still. What a compile of a chain costs beside the
 * counts rises with the square of its length, so a chain long enough to run out of the stack a thread
 * is given by default would make every case here wait on that; a chain this long runs out of this
 * stack wherever a count is asked as it is reached.
 */
class ACountOfAChainOfNamesIsNotTakenOnTheCallStackTest {

    private static final String ID = "chain.sou";

    private static final long STACK = 256L << 10;

    /** Halved twice by {@link #aChainTwiceAsLongOpensTwiceAsManyNames}, so a multiple of four. */
    private static final int LINKS = 120;

    private static final String UNBOUNDED = "";
    private static final String BOUNDED = "    invariant value >= 1 && value <= 9\n";

    /** {@code T1} to {@code T<links>} in {@code module}, each wrapping {@code shape} of the one
     *  before, and the first wrapping {@code bottom}. */
    private static String chain(String module, String imports, String bottom, String rule,
                                int links, String shape) {
        String name = module.equals("chain") ? "T" : "L";
        StringBuilder src = new StringBuilder("module " + module + " exposing ( " + name + links
                + " )\n\n").append(imports).append("data ").append(name).append("1 = ")
                .append(bottom).append('\n').append(rule);
        for (int i = 2; i <= links; i++) {
            src.append("data ").append(name).append(i).append(" = ")
                    .append(shape.formatted(name + (i - 1))).append('\n');
        }
        return src.toString();
    }

    private static String chain(String rule) {
        return chain("chain", "", "Int", rule, LINKS, "%s");
    }

    private static Compilation compiled(Map<String, String> byId) {
        Compilation c = Compilation.ofDocuments(new LinkedHashMap<>(byId), Set.of(),
                ModulePath.EMPTY);
        c.answerEverything();
        return c;
    }

    private static Compilation compiled(String source) {
        return compiled(Map.of(ID, source));
    }

    /**
     * What the compiler said, having got to the end of saying it.
     *
     * <p>A compile that ran out of room says so as a diagnostic of its own rather than throwing, so a
     * stack this is about is asked for in what was said as well as in what was thrown.
     */
    private static List<String> said(Compilation c) {
        List<String> out = new ArrayList<>();
        c.db().allReports().forEach(each -> out.add(each.module() + " "
                + each.report().diagnostic().code() + " " + each.report().diagnostic().said()));
        assertTrue(out.stream().noneMatch(each -> each.contains(" E2108 ")),
                () -> "the compile ran out of room: " + out);
        return out;
    }

    @Test
    void compiledOnASmallStack() {
        onASmallStack(() -> said(compiled(chain(BOUNDED))));
    }

    @Test
    void compiledAgainAndEditedAtTheBottomOnASmallStack() {
        List<String> afresh = onASmallStack(() -> said(compiled(chain(BOUNDED))));
        List<String> edited = onASmallStack(() -> {
            Compilation c = compiled(chain(UNBOUNDED));
            c.answerEverything();
            c.update(Map.of(ID, chain(BOUNDED)), Set.of());
            c.answerEverything();
            return said(c);
        });

        assertEquals(afresh, edited,
                "a store edited at the bottom of the chain says what a fresh one does");
    }

    /**
     * Each name wrapping a list of the one before, which a count reads under no rule below the
     * first list — and reads the same way at every link, so it is not read again at each.
     */
    @Test
    void aChainOfNamesEachWrappingAListOfTheOneBefore() {
        onASmallStack(() -> said(compiled(chain("chain", "", "Int", BOUNDED, LINKS, "List<%s>"))));
    }

    /**
     * A chain that starts in one module and goes on in another. The module read from counts what
     * it reaches of the other in the same order as its own, so the other's links are answered
     * before the first of its own that reads them.
     */
    @Test
    void aChainCrossingIntoTheModuleItIsReadFrom() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("lower.sou", chain("lower", "", "Int", BOUNDED, LINKS / 2, "%s"));
        byId.put(ID, chain("chain", "import lower ( L" + LINKS / 2 + " )\n\n",
                "L" + LINKS / 2, UNBOUNDED, LINKS / 2, "%s"));
        onASmallStack(() -> said(compiled(byId)));
    }

    /**
     * What each link's count is recorded as reading is the link beneath it and not the chain, and
     * the module's counts read each link once.
     */
    @Test
    void eachCountReadsTheLinkItWrapsAndTheModuleReadsEachLinkOnce() {
        Compilation c = onASmallStack(() -> compiled(chain(BOUNDED)));
        said(c);
        int mostAnyLinkRead = 0;
        for (int i = 1; i <= LINKS; i++) {
            mostAnyLinkRead = Math.max(mostAnyLinkRead,
                    countsRead(c.db(), new Shapes.CardinalityOf(new TypeKey("chain", "T" + i))));
        }

        assertEquals(1, mostAnyLinkRead, "a link's count read more than the link it wraps");
        assertEquals(LINKS, countsRead(c.db(), new Shapes.CardinalitiesOf("chain")),
                "the module's counts read the links some other number of times than once each");
    }

    private static int countsRead(Db db, Key<?> key) {
        assertTrue(db.isComputed(key), () -> key + " was never asked");
        int counts = 0;
        for (Key<?> read : db.dependenciesOf(key)) {
            if (read instanceof Shapes.CardinalityOf) {
                counts++;
            }
        }
        return counts;
    }

    /** As many names opened per link however long the chain is. */
    @Test
    void aChainTwiceAsLongOpensTwiceAsManyNames() {
        long shorter = opened(LINKS / 2) - opened(LINKS / 4);
        long longer = opened(LINKS) - opened(LINKS / 2);

        assertTrue(shorter > 0, "a count of the chain opened no name, so this measures nothing");
        assertEquals(2 * shorter, longer,
                "the names opened for a chain grow faster than the chain does");
    }

    private static long opened(int links) {
        return onASmallStack(() -> {
            long before = TypeCardinality.namesOpened();
            compiled(chain("chain", "", "Int", BOUNDED, links, "%s"));
            return TypeCardinality.namesOpened() - before;
        });
    }

    private static <T> T onASmallStack(Supplier<T> body) {
        AtomicReference<T> answer = new AtomicReference<>();
        AtomicReference<Throwable> failed = new AtomicReference<>();
        Thread compiling = new Thread(null, () -> {
            try {
                answer.set(body.get());
            } catch (Throwable e) {
                failed.set(e);
            }
        }, "a small stack", STACK);
        compiling.start();
        try {
            compiling.join();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError(e);
        }
        assertNull(failed.get(), () -> String.valueOf(failed.get()));
        return answer.get();
    }
}
