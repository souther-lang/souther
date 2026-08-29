package souther.compiler.flow;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The bound on how many ways one value is read as being settled stops the work.
 *
 * <p>A rule about the work and not a property of the answer, which is the whole of why it is there.
 * Fifteen independently forked parts of one value have thirty-two thousand combinations, and a
 * reading that builds all of them and then says it will not hold them apart has already done the
 * thing the bound was written to prevent — the answer is the same and the reading is the one nobody
 * can afford.
 *
 * <p>So this counts. A time is not what is being claimed: the claim is that the reading stops
 * putting ways together once there are too many, which is a fact about how many times it asks the
 * naming to put two of them together and would go on being true on a faster machine.
 *
 * <p>And the other half goes on being read exactly. What the bound cuts off is the enumeration of
 * the ways to a value, never whether a value arrives — the two are separate readings and only one of
 * them has a bound in it.
 */
class TheBoundOnWaysStopsTheWorkAndNotOnlyTheAnswerTest {

    /** How many independently forked parts one value is made of. */
    private static final int PARTS = 15;

    /** What a reading that built the combinations before giving up would ask for. */
    private static final int WITHOUT_A_BOUND = 1 << PARTS;

    /**
     * One value made of fifteen independently forked parts.
     *
     * <p>One node and not fifteen. A sum written out is fifteen nested operators, and a reading that
     * bounds what it holds at each of them stops at the first — what the bound is for is the node
     * whose parts are all put together at once, which is what a construction is.
     */
    private static String source() {
        String params = IntStream.rangeClosed(1, PARTS)
                .mapToObj(each -> "a" + each + ": Int").collect(Collectors.joining(", "));
        String names = IntStream.rangeClosed(1, PARTS)
                .mapToObj(each -> "a" + each).collect(Collectors.joining(", "));
        String fields = IntStream.rangeClosed(1, PARTS)
                .mapToObj(each -> "f" + each + ": Int").collect(Collectors.joining(", "));
        String given = IntStream.rangeClosed(1, PARTS)
                .mapToObj(each -> "f" + each + " = if a" + each + " > 1 then 1 else 0")
                .collect(Collectors.joining(", "));
        return """
                module example.wide

                data Wide = { %s }

                behavior fee : (%s) -> Wide
                    constructs Wide

                let fee (%s) = Wide { %s }
                """.formatted(fields, params, names, given);
    }

    @Test
    void aValueSettledMoreWaysThanTheBoundHoldsIsNotBuiltFirst() {
        Core body = bodyOf(source());
        Counting naming = new Counting();
        ValueArrivals<Marks> reading = ValueArrivals.ofBody(body, naming);

        assertTrue(reading.waysAt(body) instanceof Paths.Beyond,
                "the ways are more than this naming will hold apart");
        // Loose on purpose. What it is here to catch is a reading that builds the whole product
        // first, which asks for the joins of every combination and is three orders of magnitude
        // above anything a reading that stops can spend.
        assertTrue(naming.joins < WITHOUT_A_BOUND / 8,
                "the ways were put together " + naming.joins + " times, and a reading that built "
                        + "them all before giving up would take at least " + WITHOUT_A_BOUND);
    }

    /**
     * The value arrives, and the bound had nothing to say about that.
     *
     * <p>The coupling the two halves are held to. A bound on the enumeration that reached the other
     * half would answer that a body with fifteen forks in one value arrives nowhere.
     */
    @Test
    void whatTheBodyDoesIsReadWhateverTheBoundSays() {
        Core body = bodyOf(source());
        ValueArrivals<Marks> reading = ValueArrivals.ofBody(body, new Counting());

        assertEquals(new Comes(java.util.Set.of(Truth.UNREAD)).truths(),
                reading.comesAt(body).truths(),
                "the value arrives, and which truth is not a question about a whole number");
    }

    private static Core bodyOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get("fee");
        assertNotNull(body, "the behavior under test has a body");
        return body;
    }

    /** The conditions on a way, and nothing else about them matters here. */
    private record Marks(List<String> of) { }

    /** A naming that holds two ways apart and counts how often it is asked to put two together. */
    private static final class Counting implements Naming<Marks> {

        private int joins;
        private final java.util.IdentityHashMap<Core, Integer> numbered =
                new java.util.IdentityHashMap<>();

        @Override
        public Marks nowhere() {
            return new Marks(List.of());
        }

        @Override
        public Marks join(Marks held, Marks more) {
            joins++;
            java.util.List<String> both = new java.util.ArrayList<>(held.of());
            more.of().stream().filter(each -> !both.contains(each)).forEach(both::add);
            return new Marks(List.copyOf(both));
        }

        @Override
        public Naming<Marks> under(Core.Binder binder, Core value) {
            return this;
        }

        @Override
        public Marks side(Core value, boolean held) {
            return mark(value, "cmp", held ? 1 : 0);
        }

        @Override
        public Marks matchCase(Core.Match match, int part) {
            return mark(match, "case", part);
        }

        @Override
        public Marks forkArm(Core fork, int part) {
            return mark(fork, "arm", part);
        }

        private Marks mark(Core at, String what, int part) {
            int which = numbered.computeIfAbsent(at, ignored -> numbered.size());
            return new Marks(List.of(what + "@" + which + "/" + part));
        }

        @Override
        public int mostArrivals() {
            return 2;
        }
    }
}
