package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every way a search here can fall short is one some graph in this suite reaches.
 *
 * <p>The arms are the checklist. What the conformance tests say about falling short is that it did
 * not happen over the corpus today, which is true of a mechanism that reports it and equally true of
 * one that stopped — so a way out that nothing here builds is a way out that could quietly stop
 * being reported, and an arm added to {@link Gap.Why} arrives with nobody having built the graph
 * that reaches it.
 *
 * <p>Over every searcher and not one of them. The three narrow what they look at for different
 * reasons — a walk of two answers, a walk of one, a count of what this compiler can be asked — and
 * they answer in one vocabulary so that this can be one list. Held per searcher, each of them would
 * need its own account of which arms are its own, which is the same list written three times.
 */
class EveryWayASearchFallsShortIsBuiltHereTest {

    /** Something with no equality of its own, which is what a walk is looking for. */
    private static final class Address {}

    private record Held(Object it, Address beside) {}

    /** Something whose only field is itself. Made of a thing with no equality, because a container
     *  that holds itself has an {@code equals} that never comes back. */
    private static final class Loop {
        private Loop again;
    }

    /** Something whose insides belong to a module that opens nothing here. */
    private record Dated(java.time.LocalDateTime at) {}

    @Test
    void everyWayASearchCanFallShortIsReachedByAGraphHere() throws Exception {
        assertEquals(EnumSet.allOf(Gap.Why.class), EnumSet.copyOf(reached()),
                "a way a search here can fall short that no graph in this suite reaches");
    }

    /** Every arm any searcher here produces, gathered from graphs built for it. */
    private static List<Gap.Why> reached() throws Exception {
        List<Gap> gaps = new ArrayList<>();
        pairWalks().forEach(covered -> {
            if (covered instanceof Covered.Partly<Divergence>(List<Divergence> _, List<Gap> some)) {
                gaps.addAll(some);
            }
        });
        if (walkOfOne() instanceof Covered.Partly<AnswerWalk.Found>(var _, List<Gap> some)) {
            gaps.addAll(some);
        }
        if (aScanOfSomethingUnloadable()
                instanceof Covered.Partly<String>(List<String> _, List<Gap> some)) {
            gaps.addAll(some);
        }
        if (twoStoresAskedDifferently()
                instanceof Covered.Partly<TwoStores.Found>(var _, List<Gap> some)) {
            gaps.addAll(some);
        }
        return gaps.stream().map(Gap::why).toList();
    }

    /** The graphs that stop a walk of two answers. */
    private static List<Covered<Divergence>> pairWalks() {
        Address beside = new Address();
        Map<Object, Object> unpairable = new HashMap<>();
        unpairable.put(new Address(), "v");
        Map<Object, Object> alsoUnpairable = new HashMap<>();
        alsoUnpairable.put(new Address(), "v");
        Loop ring = new Loop();
        ring.again = ring;
        Loop alsoRing = new Loop();
        alsoRing.again = alsoRing;
        return List.of(
                Divergence.between(unpairable, alsoUnpairable),
                Divergence.between(ring, alsoRing),
                Divergence.between(new Held(new java.util.ArrayDeque<>(List.of("a")), beside),
                        new Held(new java.util.ArrayDeque<>(List.of("a")), beside)),
                Divergence.between(new Dated(java.time.LocalDateTime.of(2026, 1, 1, 0, 0)),
                        new Dated(java.time.LocalDateTime.of(2026, 1, 2, 0, 0))),
                Divergence.between(new Held(new Address(), new Address()),
                        new Held(new Address(), new Address()), 1));
    }

    /** And the one that stops a walk of one, which is the same field nothing will open. */
    private static Covered<AnswerWalk.Found> walkOfOne() {
        return AnswerWalk.of("Q", new Dated(java.time.LocalDateTime.of(2026, 1, 1, 0, 0)))
                .covered();
    }

    /** A place to count keys in, holding something that is not a class. */
    private static Covered<String> aScanOfSomethingUnloadable() throws Exception {
        Path root = Files.createTempDirectory("souther-scan");
        Path where = root.resolve("souther/compiler/query");
        Files.createDirectories(where);
        Files.writeString(where.resolve("NotAClass.class"), "this is not a class file");
        try {
            return EveryQuestionThisCompilerDeclaresIsReachedOrOutsideABatchRunTest.scanOf(root);
        } finally {
            delete(root);
        }
    }

    /** And two stores of one input where one was put a question the other was not. */
    private static Covered<TwoStores.Found> twoStoresAskedDifferently() {
        String source = """
                module m.two

                data R = { a: Int }

                behavior f : (r: R) -> Int
                let f (r) = r.a
                """;
        Compilation one = Compilation.ofSource(source, "Main");
        one.answerEverything();
        Compilation other = Compilation.ofSource(source, "Main");
        other.answerEverything();
        // One of them is asked something more than the other, which is the whole of the shape: two
        // stores over one input that were not put the same questions have nothing to be compared
        // over wherever only one of them was asked.
        other.db().ask(new Front.Behaviors(other.modules().getFirst()));

        return TwoStores.compared(one.db(), other.db());
    }

    private static void delete(Path root) throws IOException {
        try (var under = Files.walk(root)) {
            under.sorted(java.util.Comparator.reverseOrder()).forEach(each -> {
                try {
                    Files.delete(each);
                } catch (IOException opaque) {
                    // A temporary directory nobody else reads; what is left of it is the operating
                    // system's to clear.
                }
            });
        }
    }

    /**
     * And the graphs here stop something, which is what the assertion above rests on.
     *
     * <p>Every arm being reached is what that one says; a run where no graph stopped anything would
     * fail it for that reason and not for a missing arm, and the message would send a reader after
     * the mechanism rather than after the fixture that stopped working.
     */
    @Test
    void theGraphsHereStopSomething() throws Exception {
        org.junit.jupiter.api.Assertions.assertFalse(reached().isEmpty(),
                "no graph here stops any search, so the list above is empty for the wrong reason");
    }
}
